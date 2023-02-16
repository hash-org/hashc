//! Defines a category of AST expressions which can be used to determine how to
//! lower them throughout the lowering stage.

use hash_tir::terms::Term;

use super::{ty::FnCallTermKind, Builder};

/// A [Category] represents what category [ast::Expr]s belong to
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
    RValue,
}

/// Determines the category for a given expression. Note that scope
/// and paren expressions have no category.
impl<'tcx> Builder<'tcx> {
    /// Compute the [Category of a given term].
    pub(crate) fn category_of_term(&self, term: &Term) -> Category {
        match term {
            // Constants that are not primitive are dealt with as
            // RValues.
            Term::Lit(_) => Category::Constant,

            Term::FnCall(ref term) => match self.classify_fn_call_term(term) {
                FnCallTermKind::Index(..) => Category::Place,
                _ => Category::RValue,
            },
            Term::Access(..) | Term::Ref(..) | Term::Deref(..) | Term::Var(..) => Category::Place,

            // Everything else is considered as an RValue of some kind.
            _ => Category::RValue,
        }
    }
}
