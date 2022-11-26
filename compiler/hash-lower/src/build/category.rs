//! Defines a category of AST expressions which can be used to determine how to
//! lower them throughout the lowering stage.

use hash_ast::ast::{AstNodeRef, Expr, LitExpr};

/// A [Category] represents what category [Expr]s belong to
/// when they are being lowered. Depending on the category, we
/// might emit different code when dealing with temporaries, etc.
#[derive(Debug, PartialEq)]
pub(crate) enum Category {
    // An assignable memory location like `x`, `x.f`, `foo()[3]`, that
    // sort of thing. Something that could appear on the LHS of an `=`
    // sign.
    Place,

    // A literal like `23` or `"foo"`. Does not include constant
    // expressions like `3 + 5`.
    Constant,

    // Something that generates a new value at runtime, like `x + y`
    // or `foo()`.
    Rvalue,
}

/// Determines the category for a given expression. Note that scope
/// and paren expressions have no category.
impl Category {
    pub(crate) fn of(expr: AstNodeRef<'_, Expr>) -> Self {
        match expr.body() {
            // Constants that are not primitive are dealt with as
            // RValues.
            Expr::Lit(LitExpr { data }) if data.is_primitive() => Self::Constant,

            Expr::Access(..)
            | Expr::Index(..)
            | Expr::Ref(..)
            | Expr::Deref(..)
            | Expr::Variable(..) => Self::Place,

            // Everything else is considered as an RValue of some kind.
            _ => Self::Rvalue,
        }
    }
}
