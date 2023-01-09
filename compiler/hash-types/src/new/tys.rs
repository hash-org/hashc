//! Definitions related to types.

use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_utils::{
    new_store_key,
    store::{CloneStore, DefaultStore},
};

use super::{
    environment::env::{AccessToEnv, WithEnv},
    holes::HoleId,
    symbols::Symbol,
};
use crate::new::{data::DataTy, fns::FnTy, refs::RefTy, terms::TermId, tuples::TupleTy};

/// The type of types, i.e. a universe.
#[derive(Debug, Clone, Copy)]
pub struct UniverseTy {
    /// The size of the universe
    ///
    /// `Universe(n + 1)` includes everything inside `Universe(n)` as well as
    /// the term `Universe(n)` itself.
    ///
    /// Root universe is Universe(0).
    pub size: usize,
}

/// Represents a type in a Hash program.
#[derive(Debug, Clone, Copy, From)]
pub enum Ty {
    /// A term which evaluates to a type.
    Eval(TermId),

    /// Type hole.
    ///
    /// Invariant: `hole.kind == HoleKind::Ty`
    Hole(HoleId),

    /// Type variable
    Var(Symbol),

    /// Tuple type
    Tuple(TupleTy),

    /// Function type
    Fn(FnTy),

    /// Reference type
    Ref(RefTy),

    /// A user-defined data type
    Data(DataTy),

    /// The universe type
    Universe(UniverseTy),
}

new_store_key!(pub TyId);
pub type TyStore = DefaultStore<TyId, Ty>;

/// Infer the type of the given term, returning its type.
#[derive(Debug, Clone, Copy)]
pub struct TypeOfTerm {
    pub term: TermId,
}

impl fmt::Display for &UniverseTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.size {
            0 => write!(f, "Type"),
            n => write!(f, "Type({n})"),
        }
    }
}

impl fmt::Display for WithEnv<'_, TyId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.env().with(&self.env().stores().ty().get(self.value)))
    }
}

impl fmt::Display for WithEnv<'_, &Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            Ty::Eval(eval_ty) => {
                write!(f, "{{{}}}", self.env().with(*eval_ty))
            }
            Ty::Hole(hole) => write!(f, "{}", self.env().with(*hole)),
            Ty::Var(resolved_var) => write!(f, "{}", self.env().with(*resolved_var)),
            Ty::Tuple(tuple_ty) => write!(f, "{}", self.env().with(tuple_ty)),
            Ty::Fn(fn_ty) => write!(f, "{}", self.env().with(fn_ty)),
            Ty::Ref(ref_ty) => write!(f, "{}", self.env().with(ref_ty)),
            Ty::Data(data_ty) => write!(f, "{}", self.env().with(data_ty)),
            Ty::Universe(universe_ty) => write!(f, "{universe_ty}"),
        }
    }
}

impl fmt::Display for WithEnv<'_, &TypeOfTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "typeof {}", self.env().with(self.value.term))
    }
}
