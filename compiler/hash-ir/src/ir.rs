//! Hash Compiler Intermediate Representation (IR) crate. This module is still
//! under construction and is subject to change.

use hash_source::{
    constant::{InternedFloat, InternedInt, InternedStr},
    location::Span,
};

/// Represents the type layout of a given expression.
#[derive(Debug, PartialEq, Eq)]
pub enum Ty<'i> {
    /// `usize` type, machine specific unsigned pointer
    USize,
    /// `u8` type, 8bit unsigned integer
    U8,
    /// `u16` type, 16bit unsigned integer
    U16,
    /// `u32` type, 32bit unsigned integer
    U32,
    /// `u64` type, 64bit unsigned integer
    U64,
    /// `isize` type, machine specific unsigned pointer
    ISize,
    /// `i8` type, 8bit signed integer
    I8,
    /// `i16` type, 16bit signed integer
    I16,
    /// `i32` type, 32bit signed integer
    I32,
    /// `i64` type, 64bit signed integer
    I64,
    /// `f32` type, 32bit float
    F32,
    /// `f64` type, 64bit float
    F64,
    /// `char` type, 32bit characters
    Char,
    /// A `void` type
    Void,
    /// Represents any collection of types in a specific order.
    Structural(&'i [Ty<'i>]),
    /// Essentially an enum representation
    Union(&'i [Ty<'i>]),
    /// Pointer that points to some type
    Ptr(&'i Ty<'i>),
    /// Raw Pointer that points to some type
    RawPtr(&'i Ty<'i>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Const {
    Char(char),
    Int(InternedInt),
    Float(InternedFloat),

    /// String has to become a struct that has a pointer
    /// to bytes and a length of bytes.
    ///
    /// ```ignore
    /// str := struct(data: &raw u8, len: usize);
    /// ```
    Str(InternedStr),
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
    kind: ExprKind<'i>,
    span: Span,
}

/// Essentially a register for a value
#[derive(Debug, PartialEq, Eq)]
pub struct LocalDecl<'a> {
    /// Mutability of the local
    mutability: Mutability,

    /// The type of the local
    ty: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct LocalIdx {
    index: usize,
}

/// The kind of an expression
#[derive(Debug, PartialEq, Eq)]
pub enum ExprKind<'i> {
    /// Filler kind when expressions are optimised out or removed for other
    /// reasons.
    Nop,
    /// A constant value.
    Const(Const),

    /// A local variable value
    Local(LocalIdx),

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
    /// An assignment expression, a right hand-side expression is assigned to a
    /// left hand-side pattern e.g. `x = 2`
    Assign(LocalIdx, &'i Expr<'i>),
    /// An expression which represents a re-assignment to a pattern with a right
    /// hand-side expression and a binary operator that combines assignment
    /// and an operator, e.g. `x += 2`
    AssignOp(LocalIdx, BinOp, &'i Expr<'i>),
    /// An expression which is taking the address of another expression with an
    /// mutability modifier e.g. `&mut x`.
    AddrOf(Mutability, &'i Expr<'i>, AddressMode),

    /// Essentially a `jump if <0> to <1> else go to <2>`
    Conditional(&'i mut Expr<'i>, BlockIdx, BlockIdx),
}

#[derive(Debug, PartialEq, Eq)]
pub enum AddressMode {
    Raw,
    Smart,
}

#[derive(Debug, PartialEq, Eq)]
pub struct BlockIdx(usize);

/// Essentially a block
#[derive(Debug, PartialEq, Eq)]
pub struct BasicBlock<'i> {
    exprs: &'i [Expr<'i>],
}
