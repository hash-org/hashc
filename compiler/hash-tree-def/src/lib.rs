#![allow(dead_code)]

mod definitions;
mod parsing;

use proc_macro::TokenStream;
use syn::parse_macro_input;

use self::definitions::TreeDef;

const NODE_ATTR_NAME: &str = "tree_node";
const NODE_TYPE_NAME: &str = "Node";
const NODES_TYPE_NAME: &str = "Nodes";

#[proc_macro]
pub fn define_tree(input: TokenStream) -> TokenStream {
    let _input = parse_macro_input!(input as TreeDef);
    todo!()
}
