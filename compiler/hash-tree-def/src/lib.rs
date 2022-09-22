//! This crate defines a macro [`define_tree`] that can be used to define a tree
//! structure comprised of nodes. The macro will generate visitor and walker
//! implementations for the given tree.

mod definitions;
mod emit;
mod parse;
mod validate;

use emit::emit_tree;
use syn::parse_macro_input;
use validate::validate_tree_def;

use self::definitions::TreeDef;

/// Helper to return a syn error as a compiler error if one of the stages fails.
macro_rules! try_syn_err {
    ($x:expr) => {
        match $x {
            Ok(value) => value,
            Err(error) => return error.to_compile_error().into(),
        }
    };
}

///! Define a tree structure.
///
/// @@Todo: docs
#[proc_macro]
pub fn define_tree(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let def = parse_macro_input!(input as TreeDef);
    try_syn_err!(validate_tree_def(&def));
    let result = { try_syn_err!(emit_tree(&def)) };
    proc_macro::TokenStream::from(result)
}
