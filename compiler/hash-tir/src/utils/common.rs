use hash_utils::stream_less_writeln;

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

pub fn dump_tir(value: impl ToString) {
    stream_less_writeln!("[TIR dump]:\n{}", value.to_string());
}
