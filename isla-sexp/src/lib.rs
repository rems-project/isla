// BSD 2-Clause License
//
// Copyright (c) 2022 Alasdair Armstrong
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

use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::{parse_macro_input, Expr, ExprPath, Result, Token};

fn alloc_expr(sexps: &Expr, expr: &Expr, id: &mut u32, toks: &mut TokenStream) -> TokenStream {
    if let Expr::Array(arr) = expr {
        match &arr.elems[0] {
            Expr::Path(ExprPath { path, .. }) if path.segments.len() == 1 => {
                let sexp_fn = &path.segments[0].ident;
                let tmp = format_ident!("__sexp_tmp_{}", id);
                *id += 1;
                let mut args: Vec<TokenStream> = Vec::new();
                for arg_expr in arr.elems.iter().skip(1) {
                    args.push(alloc_expr(sexps, arg_expr, id, toks))
                }
                toks.extend(match sexp_fn.to_string().as_ref() {
                    "bits" => quote!(let #tmp = #sexps.alloc(Sexp::Bits(#(#args),*));),
                    "atom" => quote!(let #tmp = #sexps.alloc(Sexp::Atom(#(#args),*));),
                    "list" => quote!(let #tmp = #sexps.alloc(Sexp::List(vec![#(#args),*]));),
                    "var" => quote!(let #tmp = #sexps.alloc(Sexp::Symbolic(#(#args),*));),
                    _ => {
                        quote!(let #tmp = #sexps.alloc(Sexp::List(vec![#sexps.#sexp_fn, #(#args),*]));)
                    }
                });
                tmp.to_token_stream()
            }
            _ => expr.to_token_stream(),
        }
    } else if matches!(expr, Expr::Closure(..)) {
        let tmp = format_ident!("__sexp_tmp_{}", id);
        *id += 1;
        toks.extend(quote!(let #tmp = (#expr)(#sexps);));
        tmp.to_token_stream()
    } else {
        expr.to_token_stream()
    }
}

struct SexpMacroInput {
    arena: Expr,
    expr: Expr,
}

impl Parse for SexpMacroInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let arena = input.parse()?;
        input.parse::<Token![,]>()?;
        let expr = input.parse()?;
        Ok(SexpMacroInput { arena, expr })
    }
}

#[proc_macro]
pub fn sexp(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as SexpMacroInput);

    let mut toks = TokenStream::new();
    let mut id = 0;
    let var = alloc_expr(&input.arena, &input.expr, &mut id, &mut toks);

    quote!({
        #toks
        #var
    })
    .into()
}
