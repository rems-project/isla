// MIT License
//
// Copyright (c) 2019 Alasdair Armstrong
//
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use std::collections::HashMap;

use crate::ir::*;

struct Env {
    registers: HashMap<u32, Ty<u32>>,
    functions: HashMap<u32, (Vec<Ty<u32>>, Ty<u32>)>,
}

pub enum TypeError {
    DuplicateRegister(u32),
    DuplicateFunction(u32),
    UndeclaredFunction(u32),
    BadArgument(u32, u32),
    Shadowing(u32, u32),
}

impl Env {
    fn new<B>(defs: &[Def<u32, B>]) -> Result<Self, TypeError> {
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

    fn get_fn_ty(&self, name: u32) -> Result<(Vec<Ty<u32>>, Ty<u32>), TypeError> {
        match self.functions.get(&name) {
            Some(fn_ty) => Ok(fn_ty.clone()),
            None => Err(TypeError::UndeclaredFunction(name)),
        }
    }
}

fn check_def<B>(env: &Env, def: &mut Def<u32, B>) -> Result<(), TypeError> {
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

pub fn check<B>(defs: &mut [Def<u32, B>]) -> Result<(), TypeError> {
    let env = Env::new(defs)?;
    for def in defs {
        check_def(&env, def)?
    }
    Ok(())
}
