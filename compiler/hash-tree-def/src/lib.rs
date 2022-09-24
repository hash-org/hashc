//! This crate defines a macro [`define_tree!`] that can be used to define a
//! tree structure comprised of nodes. The macro will generate visitor and
//! walker implementations for the given tree.

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

/// Define a tree structure.
///
/// This macro will generate a tree structure comprised of nodes.
///
/// # Examples
///
/// The following tree definition:
///
/// ```ignore
/// define_tree! {
///     opts! {{
///         node_type_name: AstNode,
///         nodes_type_name: AstNodes,
///         visitor_trait_base_name: AstVisitor,
///         visitor_node_ref_base_type_name: AstNodeRef,
///         get_ref_from_node_function_base_name: ast_ref,
///         ref_change_body_function_base_name: with_body,
///     }}
///     #[node]
///     pub struct Foo {
///         bar: OptionalChild!(Bar),
///     }
///     #[node]
///     pub struct Bar {
///         foo: Children!(Foo),
///     }
///     #[node]
///     pub enum Baz {
///         Foo(Bar),
///         Bar(Foo),
///     }
/// }
/// ```
///
/// will generate nodes `Foo`, `Bar`, and `Baz`, with the structure above, using
/// the `AstNode` and `AstNodes` types for nodes and node lists.
///
/// It will also generate:
/// - A visitor trait for the tree (configurable name by `opts!` macro), which
///   contains `visit_*` methods for each tree node. Each visit method has a
///   different return type (declared in the trait). A mutable and an immutable
///   version of this trait are created.
/// - A walker module for the tree (`walk`/`walk_mut`), which contains `walk_*`
///   methods for each tree node. Each walk method visits its children (using
///   the visitor) and returns the result as a structure mirroring the original
///   node definition. For enums with variants all having a single member, the
///   walker will also generate a `walk_*_same_children` function that will
///   visit the enum member after matching on it, and return the result
///   directly.
#[proc_macro]
pub fn define_tree(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let def = parse_macro_input!(input as TreeDef);
    try_syn_err!(validate_tree_def(&def));
    let result = { try_syn_err!(emit_tree(&def)) };
    proc_macro::TokenStream::from(result)
}
