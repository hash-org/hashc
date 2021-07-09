#![feature(proc_macro_span)]

use std::path::PathBuf;

use proc_macro::{Span, TokenStream};
use syn::{
    parse::{Parse, ParseBuffer, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    token::Comma,
    Expr, LitStr,
};
use quote::quote;

struct GenerateTestsInput {
    path: String,
    func: Expr,
}

impl Parse for GenerateTestsInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut result = Punctuated::<Expr, Comma>::parse_terminated(input)?;
        let args_err = || syn::Error::new(input.span(), "Expecting two arguments to macro");

        let func = result.pop().ok_or_else(args_err)?;
        let str = result.pop().ok_or_else(args_err)?;

        if !result.is_empty() {
            return Err(args_err());
        }

        let str_lit_err = || syn::Error::new_spanned(str.value(), "Expecting string literal");

        match str.value() {
            Expr::Lit(expr_lit) => match &expr_lit.lit {
                syn::Lit::Str(str) => Ok(GenerateTestsInput {
                    path: str.value(),
                    func: func.into_value(),
                }),
                _ => Err(str_lit_err()),
            },
            _ => Err(str_lit_err()),
        }
    }
}

#[proc_macro]
pub fn generate_tests(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as GenerateTestsInput);

    let test_path = PathBuf::from(&input.path);
    let call_site = Span::call_site();

    let file_path = call_site
        .source_file()
        .path()
        .parent()
        .unwrap()
        .to_owned()
        .join(test_path);

    let paths = file_path
        .read_dir()
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();

    let output = quote! {
        #[cfg(test)]
        mod tests {
            use super::*;
        
            #[test]
            fn function_name_test() {
                
            }
        }
    };

    output.into()
}
