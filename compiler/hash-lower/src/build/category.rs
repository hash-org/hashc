//! Defines a category of AST expressions which can be used to determine how to
//! lower them throughout the lowering stage.

use hash_tir::tir::{Term, Ty};

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
    RValue(RValueKind),
}

/// A sub-category for [`Category::RValue`]s, this describes which
/// specific kind of [RValue] we are dealing with, whether it will
/// be lowered with the as-rvalue or the block lowering.
#[derive(Debug, PartialEq)]
pub(crate) enum RValueKind {
    /// [RValue]s that are compiled into a destination, and likely have
    /// control flow altering effects.
    Into,

    /// [RValue]s that are used as something, they are lowered with
    /// `as_rvalue()`
    As,
}

impl Category {
    /// Determines the [Category] for a given [Term].
    pub(crate) fn of(term: &Term) -> Self {
        match term {
            // Constants that are not primitive are dealt with as
            // RValues.
            Term::Lit(_) => Category::Constant,
            Term::Index(..)
            | Term::Access(..)
            | Term::Ref(..)
            | Term::Deref(..)
            | Term::Var(..) => Category::Place,

            Term::Loop(..)
            | Term::Return(_)
            | Term::Unsafe(_)
            | Term::LoopControl(..)
            | Term::Block(_)
            | Term::Ctor(_)
            | Term::Fn(_)
            | Term::Intrinsic(_)
            | Term::Match(..)
            | Term::Call(..) => Category::RValue(RValueKind::Into),

            Term::Tuple(_)
            | Term::Assign(_)
            | Term::Array(_)
            | Term::Annot(_)
            | Term::TyOf(_)
            | Ty::DataTy(_)
            | Ty::FnTy(_)
            | Ty::TupleTy(_)
            | Ty::RefTy(_)
            | Ty::Universe(_)
            | Term::DataDef(_)
            | Term::Hole(_) => Category::RValue(RValueKind::As),
        }
    }
}
