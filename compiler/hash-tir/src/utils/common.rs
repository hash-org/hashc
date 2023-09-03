use hash_source::location::Span;
use hash_utils::stream_less_writeln;

use crate::node::HasAstNodeId;

/// Assert that the given term is of the given variant, and return it.
#[macro_export]
macro_rules! term_as_variant {
    ($self:expr, $term:expr, $variant:ident) => {{
        let term = $term;
        if let $crate::terms::Term::$variant(term) = *term {
            term
        } else {
            panic!("Expected term {} to be a {}", term, stringify!($variant))
        }
    }};
}

/// Assert that the given type is of the given variant, and return it.
#[macro_export]
macro_rules! ty_as_variant {
    ($self:expr, $ty:expr, $variant:ident) => {{
        let ty = $ty;
        if let $crate::tys::Ty::$variant(ty) = ty {
            ty
        } else {
            panic!("Expected type {} to be a {}", ty, stringify!($variant))
        }
    }};
}

/// Get the location of a location target.
pub fn get_span(target: impl HasAstNodeId) -> Option<Span> {
    target.node_id().map(|n| n.span())
}

pub fn dump_tir(value: impl ToString) {
    stream_less_writeln!("[TIR dump]:\n{}", value.to_string());
}
