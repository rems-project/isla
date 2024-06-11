// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

//! This module loads a TOML file containing configuration for a specific instruction set
//! architecture.

use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;
use toml::Value;

use crate::bitvector::BV;
use crate::ir::{IRTypeInfo, Loc, Name, Reset, Symtab, URVal, Val};
use crate::ir_lexer::new_ir_lexer;
use crate::primop_util::symbolic_from_typedefs;
use crate::smt::smtlib::Exp;
use crate::smt_parser;
use crate::source_loc::SourceLoc;
use crate::value_parser::{LocParser, URValParser, ValParser};
use crate::zencode;

fn allowed_keys(config: &Value, root: &str, allowed_keys: &[&str]) -> Result<(), String> {
    let Value::Table(tbl) = config else { return Err(format!("{} should be a toml key-value table", root)) };

    'outer: for key in tbl.keys() {
        for allowed_key in allowed_keys {
            if key == allowed_key {
                continue 'outer;
            }
        }
        return Err(format!("Key {} is not allowed in {}", key, root));
    }

    Ok(())
}

/// We make use of various external tools like an assembler/objdump utility. We want to make sure
/// they are available.
fn find_tool_path<P>(program: P) -> Result<PathBuf, String>
where
    P: AsRef<Path>,
{
    if program.as_ref().is_absolute() {
        Ok(program.as_ref().to_path_buf())
    } else {
        env::var_os("PATH")
            .and_then(|paths| {
                env::split_paths(&paths).find_map(|dir| {
                    let full_path = dir.join(&program);
                    if full_path.is_file() {
                        Some(full_path)
                    } else {
                        None
                    }
                })
            })
            .ok_or_else(|| format!("Tool {} not found in $PATH", program.as_ref().display()))
    }
}

#[derive(Debug)]
pub struct Tool {
    pub executable: PathBuf,
    pub options: Vec<String>,
}

impl Tool {
    pub fn command(&self) -> Command {
        let mut cmd = Command::new(&self.executable);
        cmd.args(&self.options);
        cmd
    }
}

fn get_tool_path(config: &Value, tool: &str) -> Result<Tool, String> {
    match config.get(tool) {
        Some(Value::String(tool)) => {
            let mut words = tool.split_whitespace();
            let program = words.next().ok_or_else(|| format!("Toolchain option {} cannot be an empty string", tool))?;
            Ok(Tool { executable: find_tool_path(program)?, options: words.map(|w| w.to_string()).collect() })
        }
        _ => Err(format!("Toolchain option {} must be specified", tool)),
    }
}

struct Toolchain {
    assembler: Tool,
    objdump: Tool,
    nm: Tool,
    linker: Tool,
}

fn get_toolchain(config: &Value, chosen: Option<&str>) -> Result<Toolchain, String> {
    use std::env::consts::*;

    // if we don't have a [[toolchain]] array just try to get values from the toplevel
    let Some(Value::Array(toolchains)) = config.get("toolchain") else {
        return Ok(Toolchain {
            assembler: get_tool_path(config, "assembler")?,
            objdump: get_tool_path(config, "objdump")?,
            nm: get_tool_path(config, "nm")?,
            linker: get_tool_path(config, "linker")?,
        });
    };

    for toolchain in toolchains {
        allowed_keys(toolchain, "[[toolchain]]", &["name", "os", "arch", "assembler", "objdump", "linker", "nm"])?;
    }

    for toolchain in toolchains {
        let Some(name) = toolchain.get("name").and_then(Value::as_str) else {
            return Err("toolchain entry must have a name field".to_string());
        };

        let os = match toolchain.get("os") {
            Some(Value::String(os)) => Some(os),
            None => None,
            Some(_) => return Err("os key must be a string in toolchain definition".to_string()),
        };

        let arch = match toolchain.get("arch") {
            Some(Value::String(arch)) => Some(arch),
            None => None,
            Some(_) => return Err("arch key must be a string in toolchain definition".to_string()),
        };

        let usable_toolchain = if let Some(chosen_name) = chosen {
            name == chosen_name
        } else {
            match (os, arch) {
                (Some(os), Some(arch)) => os == OS && arch == ARCH,
                (Some(os), None) => os == OS,
                (None, Some(arch)) => arch == ARCH,
                (None, None) => true,
            }
        };

        if usable_toolchain {
            return Ok(Toolchain {
                assembler: get_tool_path(toolchain, "assembler")?,
                objdump: get_tool_path(toolchain, "objdump")?,
                nm: get_tool_path(toolchain, "nm")?,
                linker: get_tool_path(toolchain, "linker")?,
            });
        }
    }

    if let Some(chosen_name) = chosen {
        Err(format!("Configuration file did not contain a usable toolchain named {}", chosen_name))
    } else {
        Err(format!("Configuration file did not contain a usable toolchain for os = {}, arch = {}", OS, ARCH))
    }
}

/// Get the program counter from the ISA config, and map it to the
/// correct register identifer in the symbol table.
fn get_program_counter(config: &Value, symtab: &Symtab) -> Result<Name, String> {
    match config.get("pc") {
        Some(Value::String(register)) => match symtab.get(&zencode::encode(register)) {
            Some(symbol) => Ok(symbol),
            None => Err(format!("Register {} does not exist in supplied architecture", register)),
        },
        _ => Err("Configuration file must specify the program counter via `pc = \"REGISTER_NAME\"`".to_string()),
    }
}

fn get_zero_announce_exit(config: &Value) -> Result<bool, String> {
    match config.get("zero_announce_exit") {
        Some(Value::Boolean(b)) => Ok(*b),
        Some(_) => Err("zero_announce_exit must have a boolean value if it exists in configuration".to_string()),
        None => Ok(false),
    }
}

macro_rules! event_kinds_in_table {
    ($events: ident, $kind: path, $event_str: expr, $result: ident, $symtab: ident) => {
        for (k, sets) in $events {
            let k = $symtab
                .get(&zencode::encode(k))
                .ok_or_else(|| format!(concat!("Could not find ", $event_str, " {} in architecture"), k))?;
            let sets = match sets.as_str() {
                Some(set) => vec![set],
                None => sets
                    .as_array()
                    .and_then(|sets| sets.iter().map(|set| set.as_str()).collect::<Option<Vec<_>>>())
                    .ok_or_else(|| {
                        format!(concat!(
                            "Each ",
                            $event_str,
                            " in [",
                            $event_str,
                            "s] must specify at least one cat set"
                        ))
                    })?,
            };
            for set in sets.into_iter() {
                match $result.get_mut(set) {
                    None => {
                        $result.insert(set.to_string(), vec![$kind(k)]);
                    }
                    Some(kinds) => kinds.push($kind(k)),
                }
            }
        }
    };
}

pub enum RegisterKind {
    Read(Name),
    Write(Name),
}

impl RegisterKind {
    pub fn is_read(&self) -> bool {
        matches!(self, RegisterKind::Read(_))
    }

    pub fn is_write(&self) -> bool {
        matches!(self, RegisterKind::Write(_))
    }

    pub fn name(&self) -> Name {
        match self {
            RegisterKind::Read(n) => *n,
            RegisterKind::Write(n) => *n,
        }
    }
}

fn get_register_event_sets(config: &Value, symtab: &Symtab) -> Result<HashMap<String, Vec<RegisterKind>>, String> {
    let empty = toml::value::Map::new();

    let register_reads = config
        .get("registers")
        .and_then(Value::as_table)
        .and_then(|registers| registers.get("read_events"))
        .and_then(Value::as_table)
        .unwrap_or(&empty);
    let register_writes = config
        .get("registers")
        .and_then(Value::as_table)
        .and_then(|registers| registers.get("write_events"))
        .and_then(Value::as_table)
        .unwrap_or(&empty);

    let mut result: HashMap<String, Vec<RegisterKind>> = HashMap::new();

    event_kinds_in_table!(register_reads, RegisterKind::Read, "register name", result, symtab);
    event_kinds_in_table!(register_writes, RegisterKind::Write, "register name", result, symtab);

    Ok(result)
}

#[allow(clippy::from_str_radix_10)]
fn get_table_value(config: &Value, table: &str, key: &str) -> Result<u64, String> {
    config
        .get(table)
        .and_then(|table| table.get(key).and_then(|value| value.as_str()))
        .ok_or_else(|| format!("No {}.{} found in config", table, key))
        .and_then(|value| {
            if value.len() >= 2 && &value[0..2] == "0x" {
                u64::from_str_radix(&value[2..], 16)
            } else {
                u64::from_str_radix(value, 10)
            }
            .map_err(|e| format!("Could not parse {} as a 64-bit unsigned integer in {}.{}: {}", value, table, key, e))
        })
}

fn get_table_string(config: &Value, table: &str, key: &str) -> Result<String, String> {
    config
        .get(table)
        .and_then(|table| table.get(key).and_then(|value| value.as_str()))
        .ok_or_else(|| format!("No {}.{} found in config", table, key))
        .map(|value| value.to_string())
}

fn from_toml_value<B: BV>(value: &Value, symtab: &Symtab<'_>, type_info: &IRTypeInfo) -> Result<Val<B>, String> {
    match value {
        Value::Boolean(b) => Ok(Val::Bool(*b)),
        Value::Integer(i) => Ok(Val::I128(*i as i128)),
        Value::String(s) => match ValParser::new().parse(symtab, type_info, new_ir_lexer(s)) {
            Ok(value) => Ok(value),
            Err(e) => Err(format!("Parse error when reading register value from configuration: {}", e)),
        },
        _ => Err(format!("Could not parse TOML value {} as register value", value)),
    }
}

fn from_toml_value_undef<B: BV>(
    value: &Value,
    symtab: &Symtab<'_>,
    type_info: &IRTypeInfo,
) -> Result<URVal<B>, String> {
    match value {
        Value::Boolean(b) => Ok(URVal::Init(Val::Bool(*b))),
        Value::Integer(i) => Ok(URVal::Init(Val::I128(*i as i128))),
        Value::String(s) => match URValParser::new().parse(symtab, type_info, new_ir_lexer(s)) {
            Ok(value) => Ok(value),
            Err(e) => Err(format!("Parse error when reading register value from configuration: {}", e)),
        },
        _ => Err(format!("Could not parse TOML value {} as register value", value)),
    }
}

fn get_default_registers<B: BV>(
    config: &Value,
    symtab: &Symtab,
    type_info: &IRTypeInfo,
) -> Result<HashMap<Name, Val<B>>, String> {
    let defaults = config
        .get("registers")
        .and_then(|registers| registers.as_table())
        .and_then(|registers| registers.get("defaults"));

    if let Some(defaults) = defaults {
        if let Some(defaults) = defaults.as_table() {
            defaults
                .into_iter()
                .filter_map(|(register, value)| {
                    if let Some(register) = symtab.get(&zencode::encode(register)) {
                        match from_toml_value(value, symtab, type_info) {
                            Ok(value) => Some(Ok((register, value))),
                            Err(e) => Some(Err(e)),
                        }
                    } else {
                        eprintln!(
                            "Warning: Could not find register {} when parsing registers.defaults in configuration",
                            register
                        );
                        None
                    }
                })
                .collect()
        } else {
            Err("registers.defaults should be a table of <register> = <value> pairs".to_string())
        }
    } else {
        Ok(HashMap::new())
    }
}

fn get_const_primops<B: BV>(
    config: &Value,
    symtab: &Symtab,
    type_info: &IRTypeInfo,
) -> Result<HashMap<String, Reset<B>>, String> {
    let defaults = config.get("const_primops");

    if let Some(defaults) = defaults {
        if let Some(defaults) = defaults.as_table() {
            defaults
                .into_iter()
                .filter_map(|(primop, value)| match reset_to_toml_value(value, symtab, type_info) {
                    Ok(value) => Some(Ok((primop.clone(), value))),
                    Err(e) => Some(Err(e)),
                })
                .collect()
        } else {
            Err("const_primops should be a table of <primop> = <value> pairs".to_string())
        }
    } else {
        Ok(HashMap::new())
    }
}

pub fn reset_to_toml_value<B: BV>(
    value: &Value,
    symtab: &Symtab<'_>,
    type_info: &IRTypeInfo,
) -> Result<Reset<B>, String> {
    let v = from_toml_value_undef::<B>(value, symtab, type_info)?;
    Ok(Arc::new(move |_, typedefs, solver| match &v {
        URVal::Init(value) => Ok(value.clone()),
        URVal::Uninit(ty) => symbolic_from_typedefs(ty, typedefs, solver, SourceLoc::command_line()),
    }))
}

pub type Resets<B> = Vec<(Loc<Name>, Reset<B>)>;

pub fn toml_reset_registers<B: BV>(toml: &Value, symtab: &Symtab, type_info: &IRTypeInfo) -> Result<Resets<B>, String> {
    if let Some(defaults) = toml.as_table() {
        defaults
            .into_iter()
            .map(|(register, value)| {
                if let Ok(loc) = LocParser::new().parse::<B, _, _>(symtab, type_info, new_ir_lexer(register)) {
                    if let Some(loc) = symtab.get_loc(&loc) {
                        Ok((loc, reset_to_toml_value(value, symtab, type_info)?))
                    } else {
                        Err(format!("Could not find register {} when parsing register reset information", register))
                    }
                } else {
                    Err(format!("Could not parse register {} when parsing register reset information", register))
                }
            })
            .collect()
    } else {
        Err("registers.reset should be a table of <register> = <value> pairs".to_string())
    }
}

fn get_reset_registers<B: BV>(config: &Value, symtab: &Symtab, type_info: &IRTypeInfo) -> Result<Resets<B>, String> {
    let defaults =
        config.get("registers").and_then(|registers| registers.as_table()).and_then(|registers| registers.get("reset"));

    if let Some(defaults) = defaults {
        toml_reset_registers(defaults, symtab, type_info)
    } else {
        Ok(Vec::new())
    }
}

fn get_reset_constraints(config: &Value) -> Result<Vec<Exp<Loc<String>>>, String> {
    let reset_toml =
        config.get("constraints").and_then(|section| section.as_table()).and_then(|section| section.get("reset"));
    if let Some(toml) = reset_toml {
        let constraints = toml
            .as_array()
            .and_then(|vec| vec.iter().map(|item| item.as_str()).collect::<Option<Vec<_>>>())
            .ok_or_else(|| "constraints.reset should be an array of constraint strings".to_string())?;
        constraints
            .iter()
            .map(|constraint| smt_parser::ExpParser::new().parse(constraint).map_err(|err| err.to_string()))
            .collect::<Result<Vec<_>, _>>()
    } else {
        Ok(Vec::new())
    }
}

fn get_register_renames(config: &Value, symtab: &Symtab) -> Result<HashMap<String, Name>, String> {
    let defaults = config
        .get("registers")
        .and_then(|registers| registers.as_table())
        .and_then(|registers| registers.get("renames"));

    if let Some(defaults) = defaults {
        if let Some(defaults) = defaults.as_table() {
            defaults
                .into_iter()
                .map(|(name, register)| {
                    if let Some(register) = register.as_str().and_then(|r| symtab.get(&zencode::encode(r))) {
                        Ok((name.to_string(), register))
                    } else {
                        Err(format!(
                            "Could not find register {} when parsing registers.renames in configuration",
                            register
                        ))
                    }
                })
                .collect()
        } else {
            Err("registers.names should be a table or <name> = <register> pairs".to_string())
        }
    } else {
        Ok(HashMap::new())
    }
}

fn get_translation_function(config: &Value, symtab: &Symtab) -> Result<Option<Name>, String> {
    if let Some(value) = config.get("translation_function") {
        if let Some(string) = value.as_str() {
            if let Some(name) = symtab.get(&zencode::encode(string)) {
                Ok(Some(name))
            } else {
                Err(format!("function {} does not exist in supplied architecture", string))
            }
        } else {
            Err("translation_function must be a string".to_string())
        }
    } else {
        Ok(None)
    }
}

fn get_trace_functions(config: &Value, symtab: &Symtab) -> Result<HashSet<Name>, String> {
    let trace = config.get("trace");

    if let Some(trace) = trace {
        if let Some(trace) = trace.as_array() {
            trace
                .iter()
                .map(|function| {
                    if let Some(function) = function.as_str().and_then(|f| symtab.get(&zencode::encode(f))) {
                        Ok(function)
                    } else {
                        Err(format!("Could not find function {} when parsing trace in configuration", function))
                    }
                })
                .collect()
        } else {
            Err("trace should be a list of function names".to_string())
        }
    } else {
        Ok(HashSet::new())
    }
}

fn get_registers_set<C>(config: &Value, set_name: &str, symtab: &Symtab) -> Result<C, String>
where
    C: FromIterator<Name> + Default,
{
    let ignored = config
        .get("registers")
        .and_then(|registers| registers.as_table())
        .and_then(|registers| registers.get(set_name));

    if let Some(ignored) = ignored {
        if let Some(ignored) = ignored.as_array() {
            ignored
                .iter()
                .map(|register| {
                    if let Some(register) = register.as_str().and_then(|r| symtab.get(&zencode::encode(r))) {
                        Ok(register)
                    } else {
                        Err(format!(
                            "Could not find register {} when parsing registers.{} in configuration",
                            register, set_name
                        ))
                    }
                })
                .collect()
        } else {
            Err(format!("registers.{} should be a list of register names", set_name))
        }
    } else {
        Ok(C::default())
    }
}

fn get_in_program_order(config: &Value, symtab: &Symtab) -> Result<HashSet<Name>, String> {
    let mut events = HashSet::new();

    let Some(in_po) = config.get("in_program_order") else { return Ok(events) };

    let Some(event_names) = in_po.as_array() else {
        return Err("in_program_order should be an array in configuration".to_string());
    };

    for event_name in event_names {
        let Some(s) = event_name.as_str() else {
            return Err("in_program_order should contain strings in configuration".to_string());
        };

        let Some(name) = symtab.get(&zencode::encode(s)) else {
            return Err(format!("{} is not a known event name for in_program_order in configuration", s));
        };

        events.insert(name);
    }

    Ok(events)
}

fn get_default_sizeof(config: &Value) -> Result<u32, String> {
    let Some(v) = config.get("default_sizeof") else { return Ok(4) };
    let Some(i) = v.as_integer() else { return Err("default_sizeof should be an integer".to_string()) };
    match u32::try_from(i) {
        Ok(n) => Ok(n),
        Err(e) => Err(format!("failed to parse integer in default_sizeof: {}", e)),
    }
}

pub struct ISAConfig<B> {
    /// The identifier for the program counter register
    pub pc: Name,
    /// Map from cat sets to register event kinds
    pub register_event_sets: HashMap<String, Vec<RegisterKind>>,
    /// A path to an assembler for the architecture
    pub assembler: Tool,
    /// A path to an objdump for the architecture
    pub objdump: Tool,
    /// A path to an nm for the architecture
    pub nm: Tool,
    /// A path to a linker for the architecture
    pub linker: Tool,
    /// The base address for the page tables
    pub page_table_base: u64,
    /// The number of bytes in each page
    pub page_size: u64,
    /// The base address for the page tables (stage 2)
    pub s2_page_table_base: u64,
    /// The number of bytes in each page (stage 2)
    pub s2_page_size: u64,
    /// Default commands for page table setup
    pub default_page_table_setup: String,
    /// The base address for the threads in a litmus test
    pub thread_base: u64,
    /// The top address for the thread memory region
    pub thread_top: u64,
    /// The number of bytes between each thread
    pub thread_stride: u64,
    /// The first address to use when allocating symbolic addresses
    pub symbolic_addr_base: u64,
    /// One above the maximum address to use when allocating symbolic
    /// addresses (i.e. the range is half-open `[base, top)`)
    pub symbolic_addr_top: u64,
    /// The number of bytes between each symbolic address
    pub symbolic_addr_stride: u64,
    /// Default values for specified registers
    pub default_registers: HashMap<Name, Val<B>>,
    /// Reset values for specified registers
    pub reset_registers: Vec<(Loc<Name>, Reset<B>)>,
    /// Constraints that should hold at reset_registers
    pub reset_constraints: Vec<Exp<Loc<String>>>,
    /// Constant primops
    pub const_primops: HashMap<String, Reset<B>>,
    /// Assumptions to use about function behaviour
    pub function_assumptions: Vec<(String, Vec<Option<Exp<Loc<String>>>>, Exp<Loc<String>>)>,
    /// Register synonyms to rename
    pub register_renames: HashMap<String, Name>,
    /// Registers to ignore during footprint analysis
    pub ignored_registers: HashSet<Name>,
    /// Relaxed registers
    pub relaxed_registers: HashSet<Name>,
    /// Print debug information for any function calls in this set during symbolic execution
    pub probes: HashSet<Name>,
    /// Probe information under these functions
    pub probe_functions: HashSet<Name>,
    /// Trace calls to functions in this set
    pub trace_functions: HashSet<Name>,
    /// Address translation function
    pub translation_function: Option<Name>,
    /// The abstract events that should be included in program order
    pub in_program_order: HashSet<Name>,
    /// The default size (in bytes) for memory accesses in litmus tests
    pub default_sizeof: u32,
    /// Exit if sail_instr_announce is called with a zero bitvector
    pub zero_announce_exit: bool,
}

impl<B: BV> ISAConfig<B> {
    pub fn parse(
        contents: &str,
        toolchain_name: Option<&str>,
        symtab: &Symtab,
        type_info: &IRTypeInfo,
    ) -> Result<Self, String> {
        let config = match contents.parse::<Value>() {
            Ok(config) => config,
            Err(e) => return Err(format!("Error when parsing configuration: {}", e)),
        };

        // Insert the translation_function into the set of functions
        // to trace, if it is provided by the config
        let translation_function = get_translation_function(&config, symtab)?;
        let mut trace_functions = get_trace_functions(&config, symtab)?;
        if let Some(f) = translation_function {
            trace_functions.insert(f);
        }

        let toolchain = get_toolchain(&config, toolchain_name)?;

        Ok(ISAConfig {
            pc: get_program_counter(&config, symtab)?,
            register_event_sets: get_register_event_sets(&config, symtab)?,
            assembler: toolchain.assembler,
            objdump: toolchain.objdump,
            nm: toolchain.nm,
            linker: toolchain.linker,
            page_table_base: get_table_value(&config, "mmu", "page_table_base")?,
            page_size: get_table_value(&config, "mmu", "page_size")?,
            s2_page_table_base: get_table_value(&config, "mmu", "s2_page_table_base")?,
            s2_page_size: get_table_value(&config, "mmu", "s2_page_size")?,
            default_page_table_setup: get_table_string(&config, "mmu", "default_setup")
                .unwrap_or_else(|_| String::new()),
            thread_base: get_table_value(&config, "threads", "base")?,
            thread_top: get_table_value(&config, "threads", "top")?,
            thread_stride: get_table_value(&config, "threads", "stride")?,
            symbolic_addr_base: get_table_value(&config, "symbolic_addrs", "base")?,
            symbolic_addr_top: get_table_value(&config, "symbolic_addrs", "top")?,
            symbolic_addr_stride: get_table_value(&config, "symbolic_addrs", "stride")?,
            default_registers: get_default_registers(&config, symtab, type_info)?,
            reset_registers: get_reset_registers(&config, symtab, type_info)?,
            reset_constraints: get_reset_constraints(&config)?,
            const_primops: get_const_primops(&config, symtab, type_info)?,
            function_assumptions: Vec::new(),
            register_renames: get_register_renames(&config, symtab)?,
            ignored_registers: get_registers_set(&config, "ignore", symtab)?,
            relaxed_registers: get_registers_set(&config, "relaxed", symtab)?,
            probes: HashSet::new(),
            probe_functions: HashSet::new(),
            trace_functions,
            translation_function,
            in_program_order: get_in_program_order(&config, symtab)?,
            default_sizeof: get_default_sizeof(&config)?,
            zero_announce_exit: get_zero_announce_exit(&config)?,
        })
    }

    pub fn read_event_registers(&self) -> HashSet<Name> {
        let mut registers = HashSet::new();
        for (_, regs) in self.register_event_sets.iter() {
            for reg in regs.iter() {
                if let RegisterKind::Read(name) = reg {
                    registers.insert(*name);
                }
            }
        }
        registers
    }

    pub fn write_event_registers(&self) -> HashSet<Name> {
        let mut registers = HashSet::new();
        for (_, regs) in self.register_event_sets.iter() {
            for reg in regs.iter() {
                if let RegisterKind::Write(name) = reg {
                    registers.insert(*name);
                }
            }
        }
        registers
    }

    /// Load the configuration from a TOML file.
    pub fn from_file<P>(
        hasher: &mut Sha256,
        path: P,
        toolchain_name: Option<&str>,
        symtab: &Symtab,
        type_info: &IRTypeInfo,
    ) -> Result<Self, String>
    where
        P: AsRef<Path>,
    {
        let mut contents = String::new();
        match File::open(&path) {
            Ok(mut handle) => match handle.read_to_string(&mut contents) {
                Ok(_) => (),
                Err(e) => return Err(format!("Unexpected failure while reading config: {}", e)),
            },
            Err(e) => return Err(format!("Error when loading config '{}': {}", path.as_ref().display(), e)),
        };
        hasher.input(&contents);
        hasher.input(toolchain_name.unwrap_or("default"));

        match Self::parse(&contents, toolchain_name, symtab, type_info) {
            Ok(config) => Ok(config),
            Err(msg) => Err(format!("{}: {}", path.as_ref().display(), msg)),
        }
    }
}
