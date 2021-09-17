//! Hash compiler AST operator abstract representations.    

// Types of unary operators that might need to be transformed.
pub enum UnaryOpType {
    FnCall(&'static str),
    Ref,
    Deref,
}

/// Enum representing the type of compound function that an operator represents.
pub enum OperatorFn {
    Named { name: &'static str, assigning: bool },
    LazyNamed { name: &'static str, assigning: bool },
    Compound { name: CompoundFn, assigning: bool },
}

/// Compound functions that use multiple function calls when they are transformed.
pub enum CompoundFn {
    Leq,
    Geq,
    Lt,
    Gt,
}
