//! Hash Compiler Intermediate Representation (IR) crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use hash_ast::ident::Identifier;
use hash_source::location::Span;
use hash_utils::counter;

counter! {
    name: IrId,
    counter_name: IR_ID_COUNTER,
    visibility: pub,
    method_visibility: pub,
}

// TODO: do we need namespaces, we could just de-sugar them into binds that are associated
//       with symbols?

// TODO: We could just de-sugar guard patterns into:
//
// From:
//
// ```
// match k {
//    1 if x => ...
//}
// ```
//
// Into:
// ```
// match k {
//     1 => if x {
//         ...
//     }
// }
// ```
//
// But, this means that we have to perform exhaustiveness checking before transforming into IR?

#[derive(Debug, PartialEq, Eq)]
pub enum PatKind<'i> {
    Spread,
    Ignore,
    Bind(Identifier),
    Literal(Const),
    Tuple(&'i [Pat<'i>]),
    Constructor(&'i Pat<'i>, &'i [Pat<'i>]),
    List(&'i [Pat<'i>]),
    Union(&'i [Pat<'i>]),
}


/// A Pattern within IR 
#[derive(Debug, PartialEq, Eq)]
pub struct Pat<'i> {
    /// The kind of the pattern
    kind: &'i PatKind<'i>,
    /// The span of the pattern
    span: Span,
}

#[derive(Debug, PartialEq, Eq)]
pub enum UnaryOp {
    // Bitwise logical inversion
    BitNot,
    /// Logical inversion.
    Not,
    /// The operator '-' for negation
    Neg,
}

#[derive(Debug, PartialEq, Eq)]
pub enum BinOp {
    /// '=='
    EqEq,
    /// '!='
    NotEq,
    /// '|'
    BitOr,
    /// '||'
    Or,
    /// '&'
    BitAnd,
    /// '&&'
    And,
    /// '^'
    BitXor,
    /// '^^'
    Exp,
    /// '>'
    Gt,
    /// '>='
    GtEq,
    /// '<'
    Lt,
    /// '<='
    LtEq,
    /// '>>'
    Shr,
    /// '<<'
    Shl,
    /// '+'
    Add,
    /// '-'
    Sub,
    /// '*'
    Mul,
    /// '/'
    Div,
    /// '%'
    Mod,
    /// 'as'
    As,
}

/// Mutability 
#[derive(Debug, PartialEq, Eq)]
pub enum Mutability {
    Mutable,
    Immutable,
}

/// An expression within the representation
#[derive(Debug, PartialEq, Eq)]
pub struct Expr<'i> {
    ir_id: IrId,
    kind: ExprKind<'i>,
    span: Span,
}

/// The kind of an expression
#[derive(Debug, PartialEq, Eq)]
pub enum ExprKind<'i> {
    /// Filler kind when expressions are optimised out or removed for other reasons.
    Nop,
    /// A constant value.
    Const(Const),
    /// An identity expression, essentially wrapped with an inner expression.
    Identity(&'i Expr<'i>),
    /// A unary expression with a unary operator.
    Unary(UnaryOp, &'i Expr<'i>),
    /// A binary expression with a binary operator and two inner expressions.
    Binary(BinOp, &'i Expr<'i>, &'i Expr<'i>),
    /// A function call with a number of specified arguments.
    Call(&'i Expr<'i>, &'i [Expr<'i>]),
    /// An index expression e.g. `x[3]`
    Index(&'i Expr<'i>, &'i Expr<'i>),
    /// An assignment expression, a right hand-side expression is assigned to a left hand-side
    /// pattern e.g. `x = 2`
    Assign(&'i Pat<'i>, &'i Expr<'i>),
    /// An expression which represents a re-assignment to a pattern with a right hand-side
    /// expression and a binary operator that combines assignment and an operator, e.g. 
    /// `x += 2`
    AssignOp(&'i Pat<'i>, BinOp, &'i Expr<'i>),
    /// An expression which is taking the address of another expression with an 
    /// mutability modifier e.g. `&mut x`.
    AddrOf(Mutability, &'i Expr<'i>),
}


/// Essentially a block
#[derive(Debug, PartialEq, Eq)]
pub struct Body<'i> {
    exprs: &'i [Expr<'i>],
}

#[derive(Debug, PartialEq, Eq)]
pub enum Ty {
    USize,
    Bool,
    U8,
    U16,
    U32,
    U64,
    ISize,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    Char,
    Void,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ConstData {
    data: u64,
    size: u8
}

#[derive(Debug, PartialEq, Eq)]
pub struct Const {
    data: ConstData,
    ty: Ty,
}
