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
use crate::ir::{Loc, Name, Reset, Symtab, Val};
use crate::lexer::Lexer;
use crate::value_parser::{LocParser, ValParser};
use crate::zencode;

/// We make use of various external tools like an assembler/objdump utility. We want to make sure
/// they are available.
fn find_tool_path<P>(program: P) -> Result<PathBuf, String>
where
    P: AsRef<Path>,
{
    env::var_os("PATH")
        .and_then(|paths| {
            env::split_paths(&paths)
                .filter_map(|dir| {
                    let full_path = dir.join(&program);
                    if full_path.is_file() {
                        Some(full_path)
                    } else {
                        None
                    }
                })
                .next()
        })
        .ok_or_else(|| format!("Tool {} not found in $PATH", program.as_ref().display()))
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
            let program = words.next().ok_or_else(|| format!("Configuration option {} cannot be empty", tool))?;
            Ok(Tool { executable: find_tool_path(program)?, options: words.map(|w| w.to_string()).collect() })
        }
        _ => Err(format!("Configuration option {} must be specified", tool)),
    }
}

/// Get the program counter from the ISA config, and map it to the
/// correct register identifer in the symbol table.
fn get_program_counter(config: &Value, symtab: &Symtab) -> Result<Name, String> {
    match config.get("pc") {
        Some(Value::String(register)) => match symtab.get(&zencode::encode(&register)) {
            Some(symbol) => Ok(symbol),
            None => Err(format!("Register {} does not exist in supplied architecture", register)),
        },
        _ => Err("Configuration file must specify the program counter via `pc = \"REGISTER_NAME\"`".to_string()),
    }
}

/// Get the program counter from the ISA config, and map it to the
/// correct register identifer in the symbol table.
fn get_ifetch_read_kind(config: &Value, symtab: &Symtab) -> Result<Name, String> {
    match config.get("ifetch") {
        Some(Value::String(rk)) => match symtab.get(&zencode::encode(&rk)) {
            Some(symbol) => Ok(symbol),
            None => Err(format!("Read kind {} does not exist in supplied architecture", rk)),
        },
        _ => Err("Configuration file must specify a read_kind for instruction-fetch events".to_string()),
    }
}

fn get_exclusives(config: &Value, exclusives_type: &str, symtab: &Symtab) -> Result<Vec<Name>, String> {
    match config.get(exclusives_type) {
        Some(Value::Array(exclusives)) => exclusives
            .iter()
            .map(|v| {
                let kind = v.as_str().ok_or_else(|| "Each exclusive must be a string value")?;
                match symtab.get(&zencode::encode(kind)) {
                    Some(symbol) => Ok(symbol),
                    None => Err(format!("Exclusive kind {} does not exist in supplied architecture", kind)),
                }
            })
            .collect::<Result<_, _>>(),
        _ => Err("Configuration file must specify some exclusives".to_string()),
    }
}

#[derive(Debug)]
pub enum Kind<A> {
    Read(A),
    Write(A),
    CacheOp(A),
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

fn get_event_sets(config: &Value, symtab: &Symtab) -> Result<HashMap<String, Vec<Kind<Name>>>, String> {
    let reads =
        config.get("reads").and_then(Value::as_table).ok_or_else(|| "Config file has no [reads] table".to_string())?;
    let writes = config
        .get("writes")
        .and_then(Value::as_table)
        .ok_or_else(|| "Config file has no [writes] table".to_string())?;
    let cache_ops = config
        .get("cache_ops")
        .and_then(Value::as_table)
        .ok_or_else(|| "Config file has no [cache_ops] table".to_string())?;
    
    let mut result: HashMap<String, Vec<Kind<Name>>> = HashMap::new();

    event_kinds_in_table!(reads, Kind::Read, "read_kind", result, symtab);
    event_kinds_in_table!(writes, Kind::Write, "write_kind", result, symtab);
    event_kinds_in_table!(cache_ops, Kind::CacheOp, "cache_op_kind", result, symtab);

    Ok(result)
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

fn from_toml_value<B: BV>(value: &Value) -> Result<Val<B>, String> {
    match value {
        Value::Boolean(b) => Ok(Val::Bool(*b)),
        Value::Integer(i) => Ok(Val::I128(*i as i128)),
        Value::String(s) => match ValParser::new().parse(Lexer::new(&s)) {
            Ok(value) => Ok(value),
            Err(e) => Err(format!("Parse error when reading register value from configuration: {}", e)),
        },
        _ => Err(format!("Could not parse TOML value {} as register value", value)),
    }
}

fn get_default_registers<B: BV>(config: &Value, symtab: &Symtab) -> Result<HashMap<Name, Val<B>>, String> {
    let defaults = config
        .get("registers")
        .and_then(|registers| registers.as_table())
        .and_then(|registers| registers.get("defaults"));

    if let Some(defaults) = defaults {
        if let Some(defaults) = defaults.as_table() {
            defaults
                .into_iter()
                .map(|(register, value)| {
                    if let Some(register) = symtab.get(&zencode::encode(register)) {
                        match from_toml_value(value) {
                            Ok(value) => Ok((register, value)),
                            Err(e) => Err(e),
                        }
                    } else {
                        Err(format!(
                            "Could not find register {} when parsing registers.defaults in configuration",
                            register
                        ))
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

pub fn reset_to_toml_value<B: BV>(value: &Value) -> Result<Reset<B>, String> {
    if let Err(e) = from_toml_value::<B>(value) {
        return Err(e);
    };

    let value = value.clone();
    Ok(Arc::new(move |_, _| Ok(from_toml_value(&value).unwrap())))
}

pub fn toml_reset_registers<B: BV>(toml: &Value, symtab: &Symtab) -> Result<HashMap<Loc<Name>, Reset<B>>, String> {
    if let Some(defaults) = toml.as_table() {
        defaults
            .into_iter()
            .map(|(register, value)| {
                let lexer = Lexer::new(&register);
                if let Ok(loc) = LocParser::new().parse::<B, _, _>(lexer) {
                    if let Some(loc) = symtab.get_loc(&loc) {
                        Ok((loc, reset_to_toml_value(value)?))
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

fn get_reset_registers<B: BV>(config: &Value, symtab: &Symtab) -> Result<HashMap<Loc<Name>, Reset<B>>, String> {
    let defaults =
        config.get("registers").and_then(|registers| registers.as_table()).and_then(|registers| registers.get("reset"));

    if let Some(defaults) = defaults {
        toml_reset_registers(defaults, symtab)
    } else {
        Ok(HashMap::new())
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

fn get_ignored_registers(config: &Value, symtab: &Symtab) -> Result<HashSet<Name>, String> {
    let ignored = config
        .get("registers")
        .and_then(|registers| registers.as_table())
        .and_then(|registers| registers.get("ignore"));

    if let Some(ignored) = ignored {
        if let Some(ignored) = ignored.as_array() {
            ignored
                .iter()
                .map(|register| {
                    if let Some(register) = register.as_str().and_then(|r| symtab.get(&zencode::encode(r))) {
                        Ok(register)
                    } else {
                        Err(format!(
                            "Could not find register {} when parsing registers.ignore in configuration",
                            register
                        ))
                    }
                })
                .collect()
        } else {
            Err("registers.ignore should be a list of register names".to_string())
        }
    } else {
        Ok(HashSet::new())
    }
}


/// get the list of cat names for each barrier in the [barriers] section
fn get_barriers(config: &Value, symtab: &Symtab) -> Result<HashMap<Name, Vec<String>>, String> {
    if let Some(value) = config.get("barriers") {
        if let Some(table) = value.as_table() {
            let mut barriers = HashMap::new();
            for (bk, name) in table.iter() {
                let bk = match symtab.get(&zencode::encode(bk)) {
                    Some(bk) => bk,
                    None => return Err(format!("barrier_kind {} could not be found in the architecture", bk)),
                };
                let names: Vec<String> =
                    match name {
                        Value::String(s) => Ok(vec![s.to_string()]),
                        Value::Array(a) => {
                            a.iter().map(|v| v.as_str().map(String::from).ok_or("[barriers] values must be Strings or Arrays of String not Arrays of <other>")).into_iter().collect()
                        },
                        _ => Err("[barriers] values must be Strings or Arrays of String"),
                    }?;

                barriers.insert(bk, names);
            }
            Ok(barriers)
        } else {
            Err("[barriers] Must define a table of barrier_kind = name pairs".to_string())
        }
    } else {
        Ok(HashMap::new())
    }
}

pub struct ISAConfig<B> {
    /// The identifier for the program counter register
    pub pc: Name,
    /// The read_kind for instruction fetch events
    pub ifetch_read_kind: Name,
    /// Exlusive read_kinds for the architecture
    pub read_exclusives: Vec<Name>,
    /// Exlusive write_kinds for the architecture
    pub write_exclusives: Vec<Name>,
    /// Map from cat file sets to event kinds
    pub event_sets: HashMap<String, Vec<Kind<Name>>>,
    /// Map from cat file sets to event kinds
    pub register_event_sets: HashMap<String, Vec<RegisterKind>>,
    /// A path to an assembler for the architecture
    pub assembler: Tool,
    /// A path to an objdump for the architecture
    pub objdump: Tool,
    /// A path to a linker for the architecture
    pub linker: Tool,
    /// A mapping from sail barrier_kinds to their names in cat memory
    /// models
    pub barriers: HashMap<Name, Vec<String>>,
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
    pub reset_registers: HashMap<Loc<Name>, Reset<B>>,
    /// Constraints that should hold at reset_registers
    pub reset_constraints: Vec<String>,
    /// Register synonyms to rename
    pub register_renames: HashMap<String, Name>,
    /// Registers to ignore during footprint analysis
    pub ignored_registers: HashSet<Name>,
    /// Print debug information for any function calls in this set during symbolic execution
    pub probes: HashSet<Name>,
    /// Trace calls to functions in this set
    pub trace_functions: HashSet<Name>,
    /// Address translation function
    pub translation_function: Option<Name>,
}

impl<B: BV> ISAConfig<B> {
    pub fn parse(contents: &str, symtab: &Symtab) -> Result<Self, String> {
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

        Ok(ISAConfig {
            pc: get_program_counter(&config, symtab)?,
            ifetch_read_kind: get_ifetch_read_kind(&config, symtab)?,
            read_exclusives: get_exclusives(&config, "read_exclusives", symtab)?,
            write_exclusives: get_exclusives(&config, "write_exclusives", symtab)?,
            event_sets: get_event_sets(&config, symtab)?,
            register_event_sets: get_register_event_sets(&config, symtab)?,
            assembler: get_tool_path(&config, "assembler")?,
            objdump: get_tool_path(&config, "objdump")?,
            linker: get_tool_path(&config, "linker")?,
            barriers: get_barriers(&config, symtab)?,
            page_table_base: get_table_value(&config, "mmu", "page_table_base")?,
            page_size: get_table_value(&config, "mmu", "page_size")?,
            s2_page_table_base: get_table_value(&config, "mmu", "s2_page_table_base")?,
            s2_page_size: get_table_value(&config, "mmu", "s2_page_size")?,
            default_page_table_setup: get_table_string(&config, "mmu", "default_setup").unwrap_or_else(|_| String::new()),
            thread_base: get_table_value(&config, "threads", "base")?,
            thread_top: get_table_value(&config, "threads", "top")?,
            thread_stride: get_table_value(&config, "threads", "stride")?,
            symbolic_addr_base: get_table_value(&config, "symbolic_addrs", "base")?,
            symbolic_addr_top: get_table_value(&config, "symbolic_addrs", "top")?,
            symbolic_addr_stride: get_table_value(&config, "symbolic_addrs", "stride")?,
            default_registers: get_default_registers(&config, symtab)?,
            reset_registers: get_reset_registers(&config, symtab)?,
            reset_constraints: Vec::new(),
            register_renames: get_register_renames(&config, symtab)?,
            ignored_registers: get_ignored_registers(&config, symtab)?,
            probes: HashSet::new(),
            trace_functions,
            translation_function,
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

    /// Use a default configuration when none is specified
    pub fn new(symtab: &Symtab) -> Result<Self, String> {
        Self::parse(include_str!("../default_config.toml"), symtab)
    }

    /// Load the configuration from a TOML file.
    pub fn from_file<P>(hasher: &mut Sha256, path: P, symtab: &Symtab) -> Result<Self, String>
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
        Self::parse(&contents, symtab)
    }
}
