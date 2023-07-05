//! Definitions related to types.

use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_utils::store::Store;

use super::{holes::Hole, symbols::Symbol};
use crate::{
    data::DataTy, environment::stores::StoreId, fns::FnTy, refs::RefTy, terms::TermId,
    tir_debug_value_of_single_store_id, tir_single_store, tuples::TupleTy,
};

/// The type of types, i.e. a universe.
#[derive(Debug, Clone, Copy)]
pub struct UniverseTy {
    /// The size of the universe
    ///
    /// `Universe(n + 1)` includes everything inside `Universe(n)` as well as
    /// the term `Universe(n)` itself.
    ///
    /// Root universe is Universe(0).
    pub size: Option<usize>,
}

/// Represents a type in a Hash program.
#[derive(Debug, Clone, Copy, From)]
pub enum Ty {
    /// A term which evaluates to a type.
    Eval(TermId),

    /// Hole
    Hole(Hole),

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

tir_single_store!(
    store = pub TyStore,
    id = pub TyId,
    value = Ty,
    store_name = ty
);

tir_debug_value_of_single_store_id!(TyId);

/// Infer the type of the given term, returning its type.
#[derive(Debug, Clone, Copy)]
pub struct TypeOfTerm {
    pub term: TermId,
}

impl fmt::Display for UniverseTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.size {
            None => write!(f, "Type(*)"),
            Some(0) => write!(f, "Type"),
            Some(n) => write!(f, "Type({n})"),
        }
    }
}

impl fmt::Display for TyId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Eval(eval_ty) => {
                write!(f, "{{{}}}", *eval_ty)
            }
            Ty::Hole(hole) => write!(f, "{}", *hole),
            Ty::Var(resolved_var) => write!(f, "{}", *resolved_var),
            Ty::Tuple(tuple_ty) => write!(f, "{}", tuple_ty),
            Ty::Fn(fn_ty) => write!(f, "{}", fn_ty),
            Ty::Ref(ref_ty) => write!(f, "{}", ref_ty),
            Ty::Data(data_ty) => write!(f, "{}", data_ty),
            Ty::Universe(universe_ty) => write!(f, "{universe_ty}"),
        }
    }
}

impl fmt::Display for TypeOfTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "typeof {}", self.term)
    }
}
