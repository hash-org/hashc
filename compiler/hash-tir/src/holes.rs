//! Definitions related to type and term holes.

use core::fmt;

use derive_more::From;

use super::{symbols::Symbol, terms::TermId, tys::TyId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Hole(pub Symbol);

/// The kind of a hole binder.
///
/// These come in two forms, hole binders and guess binders.
///
/// A hole binder is of the form `?x: A. b`, and means that the hole `x` is free
/// in `b` and is of type `A`. A guess binder is of the form `?x=y. b`, and
/// means that the hole `x` is free in `b` and should be substituted for `y`.
/// This syntax is similar to lambda binder syntax `λx: A. b`, which is
/// `(x: A) => b` in Hash notation.
///
/// A hole binder is created to denote the type of a hole in the inner term, and
/// is turned into a guess binding if a tactic tries to fill the hole. Once all
/// hole bindings are converted into guess bindings and the resultant term
/// type-checks, the guesses are substituted in for the holes in the inner term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HoleBinderKind {
    Hole(TyId),
    Guess(TermId, TyId),
}

/// A hole binding. This is the first part of a hole binder.
#[derive(Debug, Clone, Copy, PartialEq, Eq, From)]
pub struct HoleBinding {
    pub hole: Hole,
    pub kind: HoleBinderKind,
}

/// A hole binder.
///
/// A hole binder binds a hole to a type or a guess to a term. It is a term of
/// the form `?x: A. b` or `?x=y. b`. The former is a hole binding and the
/// latter is a guess binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HoleBinder {
    pub hole: Hole,
    pub kind: HoleBinderKind,
    pub inner: TermId,
}

impl fmt::Display for Hole {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "hole{}", (self.0))
    }
}

impl fmt::Display for HoleBinder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.({})", HoleBinding::from((self.hole, self.kind)), (self.inner))
    }
}

impl fmt::Display for HoleBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            HoleBinderKind::Hole(ty) => {
                write!(f, "?{}:{}", (self.hole), (ty))
            }
            HoleBinderKind::Guess(guess, ty) => {
                write!(f, "?{}={}:{}", (self.hole), (guess), (ty))
            }
        }
    }
}
