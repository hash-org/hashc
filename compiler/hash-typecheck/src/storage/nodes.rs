//! Storage that holds type information about AST nodes.

use hash_ast::ast::AstNodeId;
use hash_utils::new_partial_store;

use super::terms::TermId;

new_partial_store!(pub NodeInfoStore<AstNodeId, TermId>);
