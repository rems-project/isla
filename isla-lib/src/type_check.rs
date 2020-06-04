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

use std::collections::HashMap;

use crate::concrete::BV;
use crate::ir::*;

struct Env {
    registers: HashMap<Name, Ty<Name>>,
    functions: HashMap<Name, (Vec<Ty<Name>>, Ty<Name>)>,
}

pub enum TypeError {
    DuplicateRegister(Name),
    DuplicateFunction(Name),
    UndeclaredFunction(Name),
    BadArgument(Name, Name),
    Shadowing(Name, Name),
}

impl Env {
    fn new<B: BV>(defs: &[Def<Name, B>]) -> Result<Self, TypeError> {
        let mut registers = HashMap::new();
        let mut functions = HashMap::new();
        for def in defs {
            match def {
                Def::Register(name, ty) => match registers.insert(*name, ty.clone()) {
                    None => (),
                    Some(_) => return Err(TypeError::DuplicateRegister(*name)),
                },
                Def::Extern(name, _, tys, ty) => match functions.insert(*name, (tys.to_vec(), ty.clone())) {
                    None => (),
                    Some(_) => return Err(TypeError::DuplicateFunction(*name)),
                },
                Def::Val(name, tys, ty) => match functions.insert(*name, (tys.to_vec(), ty.clone())) {
                    None => (),
                    Some(_) => return Err(TypeError::DuplicateFunction(*name)),
                },
                _ => (),
            }
        }
        Ok(Env { registers, functions })
    }

    fn get_fn_ty(&self, name: Name) -> Result<(Vec<Ty<Name>>, Ty<Name>), TypeError> {
        match self.functions.get(&name) {
            Some(fn_ty) => Ok(fn_ty.clone()),
            None => Err(TypeError::UndeclaredFunction(name)),
        }
    }
}

fn check_def<B: BV>(env: &Env, def: &mut Def<Name, B>) -> Result<(), TypeError> {
    if let Def::Fn(name, args, body) = def {
        let (arg_tys, ret_ty) = env.get_fn_ty(*name)?;
        let mut locals = HashMap::new();

        // Insert arguments and return type into the local scope
        locals.insert(RETURN, ret_ty);
        for (arg, ty) in args.iter().zip(arg_tys.iter()) {
            // Make sure that no function argument is the same as the special RETURN id
            if *arg == RETURN {
                return Err(TypeError::BadArgument(*name, *arg));
            };
            match locals.insert(*arg, ty.clone()) {
                None => (),
                // Don't allow functions where two arguments share the same id
                Some(_) => return Err(TypeError::BadArgument(*name, *arg)),
            }
        }
        // Insert identifiers declared in the function into the local environment
        for instr in body {
            match instr {
                Instr::Decl(id, ty) => match locals.insert(*id, ty.clone()) {
                    None => {
                        if env.registers.contains_key(id) {
                            return Err(TypeError::Shadowing(*name, *id));
                        }
                    }
                    Some(_) => return Err(TypeError::Shadowing(*name, *id)),
                },
                Instr::Init(id, ty, _) => match locals.insert(*id, ty.clone()) {
                    None => {
                        if env.registers.contains_key(id) {
                            return Err(TypeError::Shadowing(*name, *id));
                        }
                    }
                    Some(_) => return Err(TypeError::Shadowing(*name, *id)),
                },
                _ => (),
            }
        }
    }
    Ok(())
}

pub fn check<B: BV>(defs: &mut [Def<Name, B>]) -> Result<(), TypeError> {
    let env = Env::new(defs)?;
    for def in defs {
        check_def(&env, def)?
    }
    Ok(())
}
