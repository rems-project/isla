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

use libc::c_char;
use std::ffi::CStr;
use std::fs::File;
use std::io::prelude::*;
use std::ptr;

use isla_lib::ast;
use isla_lib::ast::*;
use isla_lib::ast_lexer;
use isla_lib::ast_parser;

#[no_mangle]
pub extern "C" fn isla_source_load(path: *const c_char) -> *mut Vec<ast::Def<String>> {
    let path = unsafe { CStr::from_ptr(path).to_string_lossy().into_owned() };

    let mut file = match File::open(path) {
        Ok(file) => file,
        Err(_) => return ptr::null_mut(),
    };

    let mut contents = String::new();
    match file.read_to_string(&mut contents) {
        Ok(_) => (),
        Err(_) => return ptr::null_mut(),
    };

    let lexer = ast_lexer::Lexer::new(&contents);
    let ir = match ast_parser::AstParser::new().parse(lexer) {
        Ok(ir) => ir,
        Err(_) => return ptr::null_mut(),
    };

    Box::into_raw(Box::new(ir))
}

#[no_mangle]
pub unsafe extern "C" fn isla_source_free(ir: *mut Vec<ast::Def<String>>) {
    let ir = Box::from_raw(ir);
    drop(ir)
}

#[no_mangle]
pub extern "C" fn isla_symtab_new<'ir>() -> *mut Symtab<'ir> {
    Box::into_raw(Box::new(Symtab::new()))
}

#[no_mangle]
pub unsafe extern "C" fn isla_symtab_free(symtab: *mut Symtab) {
    let symtab = Box::from_raw(symtab);
    drop(symtab)
}

#[no_mangle]
pub unsafe extern "C" fn isla_symtab_intern(
    symtab: *mut Symtab,
    ir: *const Vec<ast::Def<String>>,
    optimistic: bool,
) -> *mut Vec<ast::Def<u32>> {
    let symtab = match symtab.as_mut() {
        Some(symtab) => symtab,
        None => return ptr::null_mut(),
    };

    let ir = match ir.as_ref() {
        Some(ir) => ir,
        None => return ptr::null_mut(),
    };

    let mut ir = symtab.intern_defs(ir);
    insert_primops(&mut ir, if optimistic { AssertionMode::Optimistic } else { AssertionMode::Pessimistic });

    Box::into_raw(Box::new(ir))
}

#[no_mangle]
pub unsafe extern "C" fn isla_ir_free(ir: *mut Vec<ast::Def<u32>>) {
    let ir = Box::from_raw(ir);
    drop(ir)
}

#[no_mangle]
pub unsafe extern "C" fn isla_shared_state_new<'ir>(
    symtab: *const Symtab<'ir>,
    ir: *const Vec<ast::Def<u32>>,
) -> *mut SharedState<'ir> {
    let ir = match ir.as_ref() {
        Some(ir) => ir,
        None => return ptr::null_mut(),
    };

    let symtab = match symtab.as_ref() {
        Some(symtab) => symtab,
        None => return ptr::null_mut(),
    };

    Box::into_raw(Box::new(SharedState::new(symtab.clone(), ir)))
}

#[no_mangle]
pub unsafe extern "C" fn isla_shared_state_free(shared_state: *mut SharedState) {
    let shared_state = Box::from_raw(shared_state);
    drop(shared_state)
}
