// BSD 2-Clause License
//
// Copyright (c) 2020 Alasdair Armstrong
// Copyright (c) 2020 Brian Campbell
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

use getopts::{Matches, Options};
use isla_lib::ir_lexer::new_ir_lexer;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::error::Error;
use std::ffi::OsStr;
use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::process::exit;
use std::sync::Arc;

use isla_lib::bitvector::BV;
use isla_lib::config::ISAConfig;
use isla_lib::ir;
use isla_lib::ir::linearize;
use isla_lib::ir::partial_linearize;
use isla_lib::ir::*;
use isla_lib::ir_parser;
use isla_lib::log;
use isla_lib::primop_util::symbolic_from_typedefs;
use isla_lib::smt_parser;
use isla_lib::source_loc::SourceLoc;
use isla_lib::value_parser;
use isla_lib::zencode;

fn tool_name() -> Option<String> {
    match std::env::current_exe() {
        Ok(path) => Some(path.components().last()?.as_os_str().to_str()?.to_string()),
        Err(_) => None,
    }
}

pub fn print_usage(opts: &Options, free: &str, code: i32) -> ! {
    let tool = match tool_name() {
        Some(name) => name,
        None => "[tool]".to_string(),
    };
    let brief = format!("Usage: {} [options]{}{}", tool, if free.is_empty() { "" } else { " " }, free);
    eprint!("{}", opts.usage(&brief));
    exit(code)
}

pub fn common_opts() -> Options {
    let mut opts = Options::new();
    opts.optopt("T", "threads", "use this many worker threads", "<n>");
    opts.reqopt("A", "arch", "load architecture file", "<file>");
    opts.optopt("C", "config", "load custom config for architecture", "<file>");
    opts.optopt("", "toolchain", "use specified toolchain from config", "<name>");
    opts.optmulti("R", "register", "set a register, via the reset_registers builtin", "<register>=<value>");
    opts.optmulti("I", "initial", "set a register in the initial state", "<register>=<value>");
    opts.optflag("h", "help", "print this help message");
    opts.optflag("", "verbose", "print verbose output");
    opts.optopt("D", "debug", "set debugging flags", "<flags>");
    opts.optmulti("", "probe", "trace specified function calls or location assignments", "<id>");
    opts.optmulti("L", "linearize", "rewrite function into linear form", "<id>");
    opts.optmulti("P", "partial-linearize", "rewrite function into linear form", "<id>");
    opts.optopt("S", "source", "directory containing the Sail source used to generate the IR", "<path>");
    opts.optflag("", "test-linearize", "test that linearization rewrite has been performed correctly");
    opts.optmulti("", "abstract", "make function abstract", "<id>");
    opts.optmulti("", "debug-id", "print the name of an interned identifier (for debugging)", "<name id>");
    opts.optmulti("", "reset-constraint", "property to enforce at the reset_registers builtin", "<constraint>");
    opts.optflag("", "fork-assertions", "change assertions into explicit control flow");
    opts.optmulti("", "fun-assumption", "add an assumption about the behaviour of a Sail function", "<assumption>");
    opts
}

#[derive(Debug)]
pub enum SerializationError {
    InvalidFile,
    ArchitectureError,
    VersionMismatch { expected: String, got: String },
    IOError(std::io::Error),
}

impl fmt::Display for SerializationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use SerializationError::*;
        match self {
            InvalidFile => write!(f, "Invalid architecture file"),
            ArchitectureError => write!(f, "Failed to serialize architecture"),
            VersionMismatch { expected, got } => write!(
                f,
                "Isla version mismatch when loading pre-processed architecture: processed with {}, current version {}",
                got, expected
            ),
            IOError(err) => write!(f, "IO error when loading architecture: {}", err),
        }
    }
}

impl Error for SerializationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

#[allow(dead_code)]
pub fn write_serialized_architecture<B: BV>(
    output: &str,
    arch: Vec<Def<Name, B>>,
    symtab: &Symtab,
) -> Result<(), SerializationError> {
    use SerializationError::*;

    let mut file = File::create(output).map_err(IOError)?;

    let version = env!("ISLA_VERSION").as_bytes();

    let raw_ir = ir::serialize::serialize(arch).ok_or(SerializationError::ArchitectureError)?;
    let raw_symtab = bincode::serialize(&symtab.to_raw_table()).map_err(|_| SerializationError::ArchitectureError)?;

    file.write_all(b"ISLAARCH").map_err(IOError)?;
    file.write_all(&version.len().to_le_bytes()).map_err(IOError)?;
    file.write_all(version).map_err(IOError)?;
    file.write_all(&raw_ir.len().to_le_bytes()).map_err(IOError)?;
    file.write_all(&raw_ir).map_err(IOError)?;
    file.write_all(&raw_symtab.len().to_le_bytes()).map_err(IOError)?;
    file.write_all(&raw_symtab).map_err(IOError)?;

    Ok(())
}

pub struct DeserializedArchitecture<B> {
    ir: Vec<Def<Name, B>>,
    strings: Vec<String>,
    files: Vec<String>,
}

/// An architecture passed on the command line (via the -A flag) can
/// either be an unparsed Sail IR file, or a serialized pre-parsed
/// file.
pub enum Architecture<B> {
    Unparsed(String),
    Deserialized(DeserializedArchitecture<B>),
}

pub fn read_serialized_architecture<P, B>(input: P) -> Result<DeserializedArchitecture<B>, SerializationError>
where
    P: AsRef<Path>,
    B: BV,
{
    use SerializationError::*;

    let mut buf = File::open(input).map_err(IOError)?;

    let mut isla_magic = [0u8; 8];
    buf.read_exact(&mut isla_magic).map_err(IOError)?;
    if &isla_magic != b"ISLAARCH" {
        return Err(InvalidFile);
    }

    let mut len = [0u8; 8];

    buf.read_exact(&mut len).map_err(IOError)?;
    let mut version = vec![0; usize::from_le_bytes(len)];
    buf.read_exact(&mut version).map_err(IOError)?;

    if version != env!("ISLA_VERSION").as_bytes() {
        return Err(VersionMismatch {
            expected: env!("ISLA_VERSION").to_string(),
            got: String::from_utf8_lossy(&version).into_owned(),
        });
    }

    buf.read_exact(&mut len).map_err(IOError)?;
    let mut raw_ir = vec![0; usize::from_le_bytes(len)];
    buf.read_exact(&mut raw_ir).map_err(IOError)?;

    buf.read_exact(&mut len).map_err(IOError)?;
    let mut raw_symtab = vec![0; usize::from_le_bytes(len)];
    buf.read_exact(&mut raw_symtab).map_err(IOError)?;

    let ir: Vec<Def<Name, B>> = ir::serialize::deserialize(&raw_ir).ok_or(SerializationError::ArchitectureError)?;
    let (strings, files): (Vec<String>, Vec<String>) =
        bincode::deserialize(&raw_symtab).map_err(|_| SerializationError::ArchitectureError)?;

    Ok(DeserializedArchitecture { ir, strings, files })
}

fn parse_ir<'a, 'input, B: BV>(contents: &'input str, symtab: &'a mut Symtab<'input>) -> Vec<Def<Name, B>> {
    match ir_parser::IrParser::new().parse(symtab, new_ir_lexer(contents)) {
        Ok(ir) => ir,
        Err(parse_error) => {
            eprintln!("Parse error: {}", parse_error);
            exit(1)
        }
    }
}

fn load_ir<P, B>(hasher: &mut Sha256, file: P) -> Result<Architecture<B>, SerializationError>
where
    P: AsRef<Path>,
    B: BV,
{
    use SerializationError::*;

    let file = file.as_ref();
    if !file.exists() {
        eprintln!("-A/--architecture file '{}' does not exist", file.display());
        exit(1)
    }

    match file.extension().and_then(OsStr::to_str) {
        Some("irx") => read_serialized_architecture(file).map(Architecture::Deserialized),
        _ => {
            let mut buf = File::open(&file).map_err(IOError)?;
            let mut contents = String::new();
            buf.read_to_string(&mut contents).map_err(IOError)?;
            hasher.input(&contents);
            Ok(Architecture::Unparsed(contents))
        }
    }
}

pub struct CommonOpts<'ir, B> {
    pub num_threads: usize,
    pub arch: Vec<Def<Name, B>>,
    pub symtab: Symtab<'ir>,
    pub isa_config: ISAConfig<B>,
    pub source_path: Option<PathBuf>,
}

pub fn parse<B: BV>(hasher: &mut Sha256, opts: &Options) -> (Matches, Architecture<B>) {
    let args: Vec<String> = std::env::args().collect();

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(f) => {
            println!("{}", f);
            print_usage(opts, "", 1)
        }
    };

    if matches.opt_present("help") {
        print_usage(opts, "", 0)
    }

    let debug_opts = matches.opt_str("debug").unwrap_or_else(|| "".to_string());
    let logging_flags = (if matches.opt_present("verbose") { log::VERBOSE } else { 0u32 })
        | (if debug_opts.contains('f') { log::FORK } else { 0u32 })
        | (if debug_opts.contains('m') { log::MEMORY } else { 0u32 })
        | (if debug_opts.contains('l') { log::LITMUS } else { 0u32 })
        | (if debug_opts.contains('g') { log::GRAPH } else { 0u32 })
        | (if debug_opts.contains('p') { log::PROBE } else { 0u32 });
    log::set_flags(logging_flags);

    let arch = {
        let file = matches.opt_str("arch").unwrap();
        match load_ir(hasher, &file) {
            Ok(contents) => contents,
            Err(f) => {
                eprintln!("Error when loading architecture: {}", f);
                exit(1)
            }
        }
    };

    (matches, arch)
}

pub fn reset_from_string<B: BV>(arg: String, symtab: &Symtab) -> (Loc<Name>, Reset<B>) {
    let (loc, value) = match value_parser::UAssignParser::new().parse::<B, _, _>(symtab, new_ir_lexer(&arg)) {
        Ok((loc, value)) => {
            if let Some(loc) = symtab.get_loc(&loc) {
                (loc, value)
            } else {
                eprintln!("Register {:?} does not exist in the specified architecture", loc);
                exit(1)
            }
        }
        Err(_) => {
            eprintln!("Could not parse register assignment: {}", arg);
            exit(1)
        }
    };

    (
        loc,
        Arc::new(move |_, typedefs, solver| match &value {
            URVal::Init(value) => Ok(value.clone()),
            URVal::Uninit(ty) => symbolic_from_typedefs(ty, typedefs, solver, SourceLoc::command_line()),
        }),
    )
}

fn default_parallelism() -> usize {
    std::thread::available_parallelism().map(usize::from).unwrap_or(1)
}

pub fn parse_with_arch<'ir, B: BV>(
    hasher: &mut Sha256,
    opts: &Options,
    matches: &Matches,
    arch: &'ir Architecture<B>,
) -> CommonOpts<'ir, B> {
    let num_threads = match matches.opt_get_default("threads", default_parallelism()) {
        Ok(t) => t,
        Err(f) => {
            eprintln!("Could not parse --threads option: {}", f);
            print_usage(opts, "", 1)
        }
    };

    let (mut symtab, mut arch) = match arch {
        Architecture::Unparsed(arch) => {
            let mut symtab = Symtab::new();
            let arch = parse_ir(arch, &mut symtab);
            (symtab, arch)
        }
        Architecture::Deserialized(arch) => {
            let symtab = Symtab::from_raw_table(&arch.strings, &arch.files);
            (symtab, arch.ir.clone())
        }
    };

    let mut isa_config = if let Some(file) = matches.opt_str("config") {
        match ISAConfig::from_file(hasher, file, matches.opt_str("toolchain").as_deref(), &symtab) {
            Ok(isa_config) => isa_config,
            Err(e) => {
                eprintln!("{}", e);
                exit(1)
            }
        }
    } else {
        match ISAConfig::new(&symtab) {
            Ok(isa_config) => isa_config,
            Err(e) => {
                eprintln!("{}", e);
                exit(1)
            }
        }
    };

    matches.opt_strs("probe").iter().for_each(|arg| {
        if let Some(id) = symtab.get(&zencode::encode(arg)) {
            isa_config.probes.insert(id);
        } else {
            // Also allow raw names, such as throw_location
            if let Some(id) = symtab.get(arg) {
                isa_config.probes.insert(id);
            } else {
                eprintln!("Function {} does not exist in the specified architecture", arg);
                exit(1)
            }
        }
    });

    // Sometimes our debug output prints interned identifiers which
    // are just wrapped u32 numbers (as the code printing may not have
    // access to the symbol table). This flag allows us to print their
    // original name.
    matches.opt_strs("debug-id").iter().for_each(|arg| {
        if let Ok(id) = arg.parse::<u32>() {
            let id_str = zencode::decode(symtab.to_str(Name::from_u32(id)));
            eprintln!("Identifier {} is {}", id, id_str)
        } else {
            eprintln!("--debug-id argument '{}' must be an integer", arg);
            exit(1)
        }
    });

    matches.opt_strs("register").drain(..).for_each(|arg| {
        let (loc, reset) = reset_from_string(arg, &symtab);
        isa_config.reset_registers.push((loc, reset));
    });

    matches.opt_strs("initial").iter().for_each(|arg| {
        match value_parser::AssignParser::new().parse(&symtab, new_ir_lexer(&arg)) {
            Ok((Loc::Id(reg), value)) => {
                if let Some(reg) = symtab.get(&reg) {
                    isa_config.default_registers.insert(reg, value);
                } else {
                    eprintln!("Register {} does not exist in the specified architecture", reg);
                    exit(1)
                }
            }
            _ => {
                eprintln!("Could not parse register assignment: {}", arg);
                exit(1)
            }
        }
    });

    matches.opt_strs("abstract").iter().for_each(|arg| {
        if let Some((id, property_id)) = arg.split_once(|c| c == ' ' || c == ':') {
            let target = symtab.get(&zencode::encode(id.trim()));
            let property = symtab.get(&zencode::encode(property_id.trim()));
            if target.is_none() || property.is_none() {
                eprintln!(
                    "Function {} or property {} could not be found when processing --abstract option",
                    id, property_id
                )
            } else if ir::abstract_function_with_property(&mut arch, &mut symtab, target.unwrap(), property.unwrap())
                .is_none()
            {
                eprintln!("Failed to abstract function {}", id)
            }
        } else if let Some(target) = symtab.get(&zencode::encode(arg)) {
            ir::abstract_function(&mut arch, target)
        } else {
            eprintln!("Function {} could not be found when processing --abstract option", arg)
        }
    });

    if matches.opt_present("fork-assertions") {
        ir::assertions_to_jumps(&mut arch)
    }

    #[rustfmt::skip]
    matches.opt_strs("partial-linearize").iter().for_each(|id| {
        if let Some(target) = symtab.get(&zencode::encode(id)) {
            let mut arg_tys: Option<&[Ty<Name>]> = None;
            let mut ret_ty: Option<&Ty<Name>> = None;
 
            let mut rewrites = HashMap::new();

            for def in arch.iter() {
                match def {
                    Def::Val(f, tys, ty) if *f == target => {
                        arg_tys = Some(tys);
                        ret_ty = Some(ty)
                    }
 
                    Def::Fn(f, args, body) if *f == target => {
                        if let (Some(arg_tys), Some(ret_ty)) = (arg_tys, ret_ty) {
                            let rewritten_body = partial_linearize::partial_linearize(body.to_vec(), ret_ty, &mut symtab);
                                
                            if matches.opt_present("test-linearize") {
                                let success = linearize::self_test(
                                    num_threads,
                                    arch.clone(),
                                    symtab.clone(),
                                    &isa_config,
                                    args,
                                    arg_tys,
                                    ret_ty,
                                    body.to_vec(),
                                    rewritten_body.to_vec()
                                );
                                if success {
                                    log!(log::VERBOSE, &format!("Successfully proved linearization of {} equivalent", id))
                                } else {
                                    eprintln!("Failed to linearize {}", id);
                                    exit(1)
                                }
                            }

                            rewrites.insert(*f, rewritten_body);
                        } else {
                            eprintln!("Found function body before type signature when processing -P/--partial-linearize option for function {}", id);
                            exit(1)
                        }
                    }
 
                    _ => (),
                }
            }

            for def in arch.iter_mut() {
                if let Def::Fn(f, _, body) = def {
                    if *f == target {
                        *body = rewrites.remove(f).unwrap()
                    }
                }
            }
        } else {
            eprintln!("Function {} could not be found when processing -P/--partial-linearize option", id)
        }
    });

    #[rustfmt::skip]
    matches.opt_strs("linearize").iter().for_each(|id| {
        if let Some(target) = symtab.get(&zencode::encode(id)) {
            let mut arg_tys: Option<&[Ty<Name>]> = None;
            let mut ret_ty: Option<&Ty<Name>> = None;
 
            let mut rewrites = HashMap::new();

            for def in arch.iter() {
                match def {
                    Def::Val(f, tys, ty) if *f == target => {
                        arg_tys = Some(tys);
                        ret_ty = Some(ty)
                    }
 
                    Def::Fn(f, args, body) if *f == target => {
                        if let (Some(arg_tys), Some(ret_ty)) = (arg_tys, ret_ty) {
                            let rewritten_body = linearize::linearize(body.to_vec(), ret_ty, &mut symtab);
 
                            if matches.opt_present("test-linearize") {
                                let success = linearize::self_test(
                                    num_threads,
                                    arch.clone(),
                                    symtab.clone(),
                                    &isa_config,
                                    args,
                                    arg_tys,
                                    ret_ty,
                                    body.to_vec(),
                                    rewritten_body.to_vec()
                                );
                                if success {
                                    log!(log::VERBOSE, &format!("Successfully proved linearization of {} equivalent", id))
                                } else {
                                    eprintln!("Failed to linearize {}", id);
                                    exit(1)
                                }
                            }
 
                            rewrites.insert(*f, rewritten_body);
                        } else {
                            eprintln!("Found function body before type signature when processing -L/--linearize option for function {}", id);
                            exit(1)
                        }
                    }
 
                    _ => (),
                }
            }

            for def in arch.iter_mut() {
                if let Def::Fn(f, _, body) = def {
                    if *f == target {
                        *body = rewrites.remove(f).unwrap()
                    }
                }
            }
        } else {
            eprintln!("Function {} could not be found when processing -L/--linearize option", id)
        }
    });

    for constraint in matches.opt_strs("reset-constraint") {
        // NB: this doesn't have enough information to check if the locations exist
        match smt_parser::ExpParser::new().parse(&constraint) {
            Ok(exp) => isa_config.reset_constraints.push(exp),
            Err(e) => {
                eprintln!("Constraint parse error: {}", e);
                exit(1)
            }
        }
    }

    for assumption in matches.opt_strs("fun-assumption") {
        match smt_parser::FunAssumptionParser::new().parse(&assumption) {
            Ok(asm) => isa_config.function_assumptions.push(asm),
            Err(e) => {
                eprintln!("Function assumption parse error: {}", e);
                exit(1)
            }
        }
    }

    let source_path = matches.opt_str("source").map(PathBuf::from);

    CommonOpts { num_threads, arch, symtab, isa_config, source_path }
}
