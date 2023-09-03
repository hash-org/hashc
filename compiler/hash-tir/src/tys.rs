//! Definitions related to types.

use core::fmt;
use std::fmt::Debug;

use hash_storage::store::statics::{SequenceStoreValue, SingleStoreValue, StoreId};
use hash_utils::derive_more::From;

use super::{holes::Hole, symbols::SymbolId};
use crate::{
    args::Arg,
    data::{DataDefId, DataTy},
    environment::stores::tir_stores,
    fns::FnTy,
    node::{Node, NodeId, NodeOrigin},
    params::Param,
    refs::RefTy,
    terms::{Term, TermId},
    tir_node_single_store,
    tuples::TupleTy,
    utils::traversing::Atom,
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
    Var(SymbolId),

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

tir_node_single_store!(Ty);

/// Infer the type of the given term, returning its type.
#[derive(Debug, Clone, Copy)]
pub struct TypeOfTerm {
    pub term: TermId,
}

impl Ty {
    /// Create a type of types, i.e. small `Type`.
    pub fn small_universe(origin: NodeOrigin) -> TyId {
        Node::create(Node::at(Ty::Universe(UniverseTy { size: Some(0) }), origin))
    }

    /// Create a large type of types, i.e. `Type(n)` for some natural number
    /// `n`.
    pub fn universe(n: usize, origin: NodeOrigin) -> TyId {
        Node::create(Node::at(Ty::Universe(UniverseTy { size: Some(n) }), origin))
    }

    /// Create a type of types, with a flexible universe size, for the given
    /// type node.
    ///
    /// This is the default when `Type` is used in a type signature.
    pub fn universe_of(node: impl Into<Atom>) -> TyId {
        let node = node.into();
        Ty::flexible_universe(node.origin().inferred())
    }

    /// Create a type of types, with a flexible universe size.
    ///
    /// This is the default when `Type` is used in a type signature.
    pub fn flexible_universe(origin: NodeOrigin) -> TyId {
        Node::create(Node::at(Ty::Universe(UniverseTy { size: None }), origin))
    }

    /// Create a new empty tuple type.
    pub fn void(origin: NodeOrigin) -> TyId {
        Node::create(Node::at(
            Ty::Tuple(TupleTy { data: Node::create(Node::at(Node::<Param>::empty_seq(), origin)) }),
            origin,
        ))
    }

    /// Create a new variable type.
    pub fn var(symbol: SymbolId) -> TyId {
        Node::create(Node::at(Ty::Var(symbol), symbol.origin()))
    }

    /// Create a new hole type.
    pub fn hole(origin: NodeOrigin) -> TyId {
        Node::create(Node::at(Ty::Hole(Hole::fresh(origin)), origin))
    }

    /// Create a new data type with no arguments.
    pub fn data(data_def: DataDefId, origin: NodeOrigin) -> TyId {
        Node::create(Node::at(
            Ty::Data(DataTy {
                data_def,
                args: Node::create(Node::at(Node::<Arg>::empty_seq(), origin)),
            }),
            origin,
        ))
    }

    /// Create a new type.
    /// @@Todo: remove once location store is removed.
    pub fn from(ty: impl Into<Ty>, origin: NodeOrigin) -> TyId {
        Node::create_at(ty.into(), origin)
    }

    /// Create a new expected type for typing the given term.
    pub fn expect_same(_ty: TyId, expectation: TyId) -> TyId {
        expectation
    }

    /// Create a new expected type for typing the given term.
    pub fn expect_is(atom: impl Into<Atom>, ty: TyId) -> TyId {
        ty.borrow_mut().origin = atom.into().origin().inferred();
        ty
    }

    /// Create a new type hole for typing the given atom.
    pub fn hole_for(src: impl Into<Atom>) -> TyId {
        let src = src.into();
        let ty = Ty::hole(src.origin().inferred());
        Ty::expect_is(src, ty)
    }
}

impl TyId {
    /// Try to use the given type as a term.
    pub fn as_term(&self) -> TermId {
        match *self.value() {
            Ty::Var(var) => Term::from(var, self.origin()),
            Ty::Hole(hole) => Term::from(hole, self.origin()),
            Ty::Eval(term) => match term.try_as_ty() {
                Some(ty) => ty.as_term(),
                None => term,
            },
            _ => Term::from(*self, self.origin()),
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
        write!(f, "{}", *self.value())
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
