use hash_source::location::Span;
use hash_utils::stream_less_writeln;

use crate::{environment::stores::tir_stores, locations::LocationTarget};

/// Assert that the given term is of the given variant, and return it.
#[macro_export]
macro_rules! term_as_variant {
    ($self:expr, $term:expr, $variant:ident) => {{
        let term = $term;
        if let $crate::terms::Term::$variant(term) = *term {
            term
        } else {
            panic!("Expected term to be a {}", stringify!($variant))
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
            panic!("Expected type to be a {}", stringify!($variant))
        }
    }};
}

/// Get the location of a location target.
pub fn get_location(target: impl Into<LocationTarget>) -> Option<Span> {
    tir_stores().location().get_location(target)
}

pub fn dump_tir(value: impl ToString) {
    stream_less_writeln!("[TIR dump]:\n{}", value.to_string());
}
