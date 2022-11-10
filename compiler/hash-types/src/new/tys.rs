//! Definitions related to types.

use core::fmt;
use std::fmt::Debug;

use hash_utils::{
    new_store_key,
    store::{CloneStore, DefaultStore},
};

use super::{
    environment::{
        context::Binding,
        env::{AccessToEnv, WithEnv},
    },
    holes::HoleId,
    symbols::Symbol,
};
use crate::new::{
    data::DataTy, fns::FnTy, refs::RefTy, terms::TermId, trts::TrtBoundsId, tuples::TupleTy,
    unions::UnionTy,
};

/// The type of types, i.e. a universe.
#[derive(Debug, Clone, Copy)]
pub struct UniverseTy {
    /// The size of the universe
    ///
    /// `Universe(n + 1)` includes everything inside `Universe(n)` as well as
    /// the term `Universe(n)` itself.
    pub size: usize,

    /// Any additional bounds that types in the universe must satisfy.
    pub trait_bounds: TrtBoundsId,
}

/// The type of a meta construct, i.e. a type which cannot be given by the user.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaTy {
    /// The type of any `mod {...}` definition after arguments have been
    /// applied.
    ModDefTy,
    /// The type of any `trait {...}` definition after arguments have been
    /// applied.
    TrtDefTy,
}

/// Represents a type in a Hash program.
#[derive(Debug, Clone, Copy)]
pub enum Ty {
    /// A term which evaluates to a type.
    Eval(TermId),

    /// Type hole.
    ///
    /// Invariant: `hole.kind == HoleKind::Ty`
    Hole(HoleId),

    /// Type variable
    Var(Symbol),
    ResolvedVar(Binding),

    /// Union type
    Union(UnionTy),

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

    /// Meta type: type of definitions
    Meta(MetaTy),
}

new_store_key!(pub TyId);
pub type TyStore = DefaultStore<TyId, Ty>;

/// Infer the type of the given term, returning its type.
#[derive(Debug, Clone, Copy)]
pub struct TypeOfTerm {
    pub term: TermId,
}

impl fmt::Display for WithEnv<'_, TyId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.env().with(self.env().stores().ty().get(self.value)))
    }
}

impl fmt::Display for WithEnv<'_, Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            Ty::Eval(_) => todo!(),
            Ty::Hole(hole) => write!(f, "{}", self.env().with(hole)),
            Ty::Var(var) => write!(f, "{}", self.env().with(var)),
            Ty::ResolvedVar(resolved_var) => write!(f, "{}", self.env().with(resolved_var.name)),
            Ty::Union(_) => todo!(),
            Ty::Tuple(_) => todo!(),
            Ty::Fn(_) => todo!(),
            Ty::Ref(_) => todo!(),
            Ty::Data(_) => todo!(),
            Ty::Universe(_) => todo!(),
            Ty::Meta(meta) => match meta {
                MetaTy::ModDefTy => write!(f, "Module"),
                MetaTy::TrtDefTy => write!(f, "Trait"),
            },
        }
    }
}
