//! This crate defines a macro [`define_tree`] that can be used to define a tree
//! structure comprised of nodes. The macro will generate visitor and walker
//! implementations for the given tree.

mod definitions;
mod emitting;
mod parsing;

use emitting::emit_tree;
use proc_macro::TokenStream;
use syn::parse_macro_input;

use self::definitions::TreeDef;

///! Define a tree structure.
///
/// @@Todo: docs
#[proc_macro]
pub fn define_tree(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as TreeDef);
    emit_tree(input)
}
