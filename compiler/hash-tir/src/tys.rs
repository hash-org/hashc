//! Definitions related to types.

use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_ast::ast;
use hash_storage::{
    static_single_store,
    store::statics::{SequenceStoreValue, SingleStoreValue, StoreId},
};

use super::{holes::Hole, symbols::Symbol};
use crate::{
    args::Arg,
    ast_info::HasNodeId,
    data::{DataDefId, DataTy},
    environment::stores::tir_stores,
    fns::FnTy,
    params::Param,
    refs::RefTy,
    terms::{Term, TermId},
    tir_debug_value_of_single_store_id,
    tuples::TupleTy,
    utils::{common::get_location, traversing::Atom},
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

impl UniverseTy {
    /// A flexible universe.
    ///
    /// In other words, a universe Type(w) where w is determined at
    /// each usage.
    // @@Todo: figure out what "flexible" really means.
    pub fn is_flexible(&self) -> bool {
        self.size.is_none()
    }
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

static_single_store!(
    store = pub TyStore,
    id = pub TyId,
    value = Ty,
    store_name = ty,
    store_source = tir_stores()
);

impl HasNodeId for TyId {
    fn node_id(&self) -> Option<ast::AstNodeId> {
        tir_stores().ast_info().tys().get_node_by_data(*self)
    }
}

tir_debug_value_of_single_store_id!(TyId);

/// Infer the type of the given term, returning its type.
#[derive(Debug, Clone, Copy)]
pub struct TypeOfTerm {
    pub term: TermId,
}

impl Ty {
    /// Create a type of types, i.e. small `Type`.
    pub fn small_universe() -> TyId {
        Ty::create(Ty::Universe(UniverseTy { size: Some(0) }))
    }

    /// Create a large type of types, i.e. `Type(n)` for some natural number
    /// `n`.
    pub fn universe(n: usize) -> TyId {
        Ty::create(Ty::Universe(UniverseTy { size: Some(n) }))
    }

    /// Create a type of types, with a flexible universe size.
    ///
    /// This is the default when `Type` is used in a type signature.
    pub fn flexible_universe() -> TyId {
        Ty::create(Ty::Universe(UniverseTy { size: None }))
    }

    /// Create a new empty tuple type.
    pub fn void() -> TyId {
        Ty::create(Ty::Tuple(TupleTy { data: Param::empty_seq() }))
    }

    /// Create a new variable type.
    pub fn var(symbol: Symbol) -> TyId {
        Ty::create(Ty::Var(symbol))
    }

    /// Create a new hole type.
    pub fn hole() -> TyId {
        Ty::create(Ty::Hole(Hole::fresh()))
    }

    /// Create a new data type with no arguments.
    pub fn data(data_def: DataDefId) -> TyId {
        Ty::create(Ty::Data(DataTy { data_def, args: Arg::empty_seq() }))
    }

    /// Create a new type.
    pub fn from(ty: impl Into<Ty>) -> TyId {
        let ty = ty.into();
        let (ast_info, location) = match ty {
            Ty::Eval(term) => (term.node_id(), get_location(term)),
            Ty::Var(v) => (None, get_location(v)),
            _ => (None, None),
        };
        let created = Ty::create(ty);
        if let Some(location) = location {
            tir_stores().location().add_location_to_target(created, location);
        }
        if let Some(ast_info) = ast_info {
            tir_stores().ast_info().tys().insert(ast_info, created);
        }
        created
    }

    /// Create a new expected type for typing the given term.
    pub fn expect_same(ty: TyId, expectation: TyId) -> TyId {
        tir_stores().location().copy_location(ty, expectation);
        if let Some(ast_info) = ty.node_id() {
            tir_stores().ast_info().tys().insert(ast_info, expectation);
        }
        expectation
    }

    /// Create a new expected type for typing the given term.
    pub fn expect_is(atom: impl Into<Atom>, ty: TyId) -> TyId {
        let atom: Atom = atom.into();
        let (ast_info, location) = match atom {
            Atom::Term(origin_term) => match origin_term.value() {
                Term::Ty(ty) => (ty.node_id(), get_location(ty)),
                Term::FnRef(f) => (f.node_id(), get_location(f)),
                Term::Var(v) => (None, get_location(v)),
                _ => (origin_term.node_id(), tir_stores().location().get_location(origin_term)),
            },
            Atom::Ty(origin_ty) => {
                (origin_ty.node_id(), tir_stores().location().get_location(origin_ty))
            }
            Atom::FnDef(_) => todo!(),
            Atom::Pat(origin_pat) => {
                (origin_pat.node_id(), tir_stores().location().get_location(origin_pat))
            }
        };
        if let Some(location) = location {
            tir_stores().location().add_location_to_target(ty, location);
        }
        if let Some(ast_info) = ast_info {
            tir_stores().ast_info().tys().insert(ast_info, ty);
        }
        ty
    }

    /// Create a new type hole for typing the given atom.
    pub fn hole_for(src: impl Into<Atom>) -> TyId {
        let ty = Ty::hole();
        Ty::expect_is(src, ty)
    }
}

impl TyId {
    /// Try to use the given type as a term.
    pub fn as_term(&self) -> TermId {
        match self.value() {
            Ty::Var(var) => Term::from(var),
            Ty::Hole(hole) => Term::from(hole),
            Ty::Eval(term) => match term.try_as_ty() {
                Some(ty) => ty.as_term(),
                None => term,
            },
            _ => Term::from(*self),
        }
    }
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
