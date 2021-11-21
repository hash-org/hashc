//! Hash compiler AST operator abstract representations.    

use std::borrow::Cow;

// Types of unary operators that might need to be transformed.
pub enum UnaryOpType {
    FnCall(&'static str),
    Ref,
    Deref,
}

/// Enum representing the type of compound function that an operator represents.
/// @@Documentation: What's the difference between LazyNamed and Named? - LazyNamed operators exhibit short circuiting behaviour.
pub enum OperatorFn {
    Named {
        name: Cow<'static, str>,
        assigning: bool,
    },
    LazyNamed {
        name: Cow<'static, str>,
        assigning: bool,
    },
    Compound {
        name: CompoundFn,
        assigning: bool,
    },
}

/// Compound functions that use multiple function calls when they are transformed.
pub enum CompoundFn {
    Leq,
    Geq,
    Lt,
    Gt,
}
