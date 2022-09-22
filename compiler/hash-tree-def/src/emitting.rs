//! Functions to emit tree definitions, visitors, walkers, given a parsed
//! [`TreeDef`].
use proc_macro::TokenStream;
use quote::quote;

use crate::definitions::TreeDef;

pub(crate) fn emit_tree(def: TreeDef) -> TokenStream {
    // @@Todo: implement this
    def.other_items.iter().map(|item| -> TokenStream { quote!(#item).into() }).collect()
}
