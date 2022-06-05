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

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
pub struct Pat<'i> {
    kind: &'i PatKind<'i>,
    span: Span,
}

#[derive(Debug, PartialEq)]
pub enum UnaryOp {}

#[derive(Debug, PartialEq)]
pub enum BinOp {}

#[derive(Debug, PartialEq)]
pub struct Expr<'i> {
    ir_id: IrId,
    kind: ExprKind<'i>,
    span: Span,
}

#[derive(Debug, PartialEq)]
pub enum Mutability {
    Mutable,
    Immutable,
}

#[derive(Debug, PartialEq)]
pub enum ExprKind<'i> {
    Nop,
    Identity(&'i Expr<'i>),
    Unary(UnaryOp, &'i Expr<'i>),
    Binary(BinOp, &'i Expr<'i>, &'i Expr<'i>),
    Call(&'i Expr<'i>, &'i [Expr<'i>]),
    Index(&'i Expr<'i>, &'i Expr<'i>),
    Assign(&'i Pat<'i>, &'i Expr<'i>),
    AssignOp(&'i Pat<'i>, BinOp, &'i Expr<'i>),
    AddrOf(Mutability, &'i Expr<'i>),
}

#[derive(Debug, PartialEq)]
pub struct Body<'i> {
    exprs: &'i [Expr<'i>],
}

#[derive(Debug, PartialEq)]
pub struct Const {
    kind: ConstKind,
}

#[derive(Debug, PartialEq)]
pub enum ConstKind {}
