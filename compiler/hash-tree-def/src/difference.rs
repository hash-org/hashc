//! Contains a helper macro to get the difference of two identifier lists.

use syn::{parse::Parse, Ident};

/// Represents the difference of two lists of symbols.
pub(crate) struct Difference {
    pub symbols: Vec<Ident>,
    pub symbols_to_remove: Vec<Ident>,
    pub callback_macro: Ident,
    pub callback_macro_flag: Ident,
}

/// Parse a `Difference` from the following format:
///
/// `$($node:ident),*; $($node_to_remove:ident),*; $callback_macro:ident;
/// $callback_macro_flag:ident`
impl Parse for Difference {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let result = input.parse_terminated::<_, syn::Token![;]>(|parser| {
            let mut symbols = vec![];
            loop {
                match parser.parse::<Ident>() {
                    Ok(symbol) => symbols.push(symbol),
                    Err(_) => return Ok(symbols),
                }
                let _ = parser.parse::<syn::Token![,]>();
            }
        })?;

        if result.len() != 3 {
            return Err(syn::Error::new(
                input.span(),
                "Expected three lists of symbols separated by a semicolon.",
            ));
        }

        let symbols = result[0].clone();
        let symbols_to_remove = result[1].clone();
        let callback_macro = result[2].clone();
        if callback_macro.len() != 2 {
            return Err(syn::Error::new(
                input.span(),
                "Expected two symbols for the callback macro.",
            ));
        }

        Ok(Self {
            symbols: symbols.into_iter().collect(),
            symbols_to_remove: symbols_to_remove.into_iter().collect(),
            callback_macro: callback_macro[0].clone(),
            callback_macro_flag: callback_macro[1].clone(),
        })
    }
}
