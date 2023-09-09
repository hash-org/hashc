//! Definitions related to terms.

use core::fmt;
use std::fmt::Debug;

use hash_storage::store::{
    statics::{SequenceStoreValue, SingleStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_utils::derive_more::From;

use super::{casting::CastTerm, holes::Hole, symbols::SymbolId};
use crate::{
    access::AccessTerm,
    args::Arg,
    arrays::{ArrayTerm, IndexTerm},
    control::{LoopControlTerm, LoopTerm, MatchTerm, ReturnTerm},
    data::{CtorTerm, DataDefId, DataTy},
    environment::stores::tir_stores,
    fns::{CallTerm, FnDefId, FnTy},
    lits::LitId,
    node::{Node, NodeId, NodeOrigin},
    params::Param,
    primitives::primitives,
    refs::{DerefTerm, RefTerm, RefTy},
    scopes::{AssignTerm, BlockTerm, DeclTerm},
    tir_node_sequence_store_indirect, tir_node_single_store,
    tuples::{TupleTerm, TupleTy},
    utils::traversing::Atom,
};

/// A term that can contain unsafe operations.
#[derive(Debug, Clone, Copy)]
pub struct UnsafeTerm {
    pub inner: TermId,
}

/// Infer the type of the given term, returning its type.
#[derive(Debug, Clone, Copy)]
pub struct TyOfTerm {
    pub term: TermId,
}

/// A term in a Hash program.
///
/// This is a narrowed down version of the AST whose structure is more suitable
/// for typechecking and compile-time evaluation.
///
/// Some terms have their own IDs, such as traits, modules, datatypes,
/// constructors, etc. This is because they might have extra data attached to
/// them; for example, function definitions might have AST node IDs attached to
/// them through some secondary map.
#[derive(Debug, Clone, From, Copy)]
pub enum Term {
    // -- General --
    // Variables
    Var(SymbolId),
    // Scopes
    Block(BlockTerm),

    // -- Values --

    // Primitives
    Tuple(TupleTerm),
    Lit(LitId),

    // Constructors
    Ctor(CtorTerm),

    // Functions
    Call(CallTerm),
    Fn(FnDefId),

    // Loops
    Loop(LoopTerm),
    LoopControl(LoopControlTerm),

    // Control flow
    Match(MatchTerm),
    Return(ReturnTerm),

    // Declarations and assignments
    Decl(DeclTerm),
    Assign(AssignTerm),

    // Unsafe
    Unsafe(UnsafeTerm),

    // Access and indexing
    Access(AccessTerm),

    // Arrays
    Array(ArrayTerm),
    Index(IndexTerm),

    // Casting
    Cast(CastTerm),
    TypeOf(TyOfTerm),

    // References
    Ref(RefTerm),
    Deref(DerefTerm),

    // -- Types --
    /// Tuple type
    TupleTy(TupleTy),

    /// Function type
    FnTy(FnTy),

    /// Reference type
    RefTy(RefTy),

    /// A user-defined data type
    DataTy(DataTy),

    /// The universe type
    Universe,

    /// Holes
    Hole(Hole),
}

tir_node_single_store!(Term);
tir_node_sequence_store_indirect!(TermList[TermId]);

pub type Ty = Term;
pub type TyId = TermId;
pub type TyListId = TermListId;

impl Term {
    pub fn is_void(&self) -> bool {
        matches!(self, Term::Tuple(tuple_term) if tuple_term.data.value().is_empty())
    }

    pub fn unit(origin: NodeOrigin) -> TermId {
        Node::create(Node::at(
            Term::Tuple(TupleTerm {
                data: Node::create(Node::at(Node::<Arg>::empty_seq(), origin)),
            }),
            origin,
        ))
    }

    pub fn hole(origin: NodeOrigin) -> TermId {
        Node::create(Node::at(Term::Hole(Hole::fresh(origin)), origin))
    }

    pub fn var(symbol: SymbolId) -> TermId {
        Node::create(Node::at(Term::Var(symbol), symbol.origin()))
    }

    /// Create a new term with the given origin.
    pub fn from(term: impl Into<Term>, origin: NodeOrigin) -> TermId {
        Node::create_at(term.into(), origin)
    }

    /// Create a new term that inherits location and AST info from the given
    /// `source`.
    pub fn inherited_from(source: TermId, term: impl Into<Term>) -> TermId {
        Self::from(term, source.origin())
    }

    /// Create a type of types, with a flexible universe size, for the given
    /// type node.
    ///
    /// This is the default when `Type` is used in a type signature.
    pub fn universe_of(node: impl Into<Atom>) -> TyId {
        let node = node.into();
        Ty::universe(node.origin().inferred())
    }

    /// Create a type of types.
    pub fn universe(origin: NodeOrigin) -> TyId {
        Node::create(Node::at(Ty::Universe, origin))
    }

    /// Create a new empty tuple type.
    pub fn unit_ty(origin: NodeOrigin) -> TyId {
        Node::create(Node::at(
            Ty::TupleTy(TupleTy {
                data: Node::create(Node::at(Node::<Param>::empty_seq(), origin)),
            }),
            origin,
        ))
    }

    /// Create a new data type with no arguments.
    pub fn data_ty(data_def: DataDefId, origin: NodeOrigin) -> TyId {
        Node::create(Node::at(
            Ty::DataTy(DataTy {
                data_def,
                args: Node::create(Node::at(Node::<Arg>::empty_seq(), origin)),
            }),
            origin,
        ))
    }

    /// Create the empty type.
    pub fn never_ty(origin: NodeOrigin) -> TyId {
        Ty::from(
            DataTy {
                args: Node::create_at(Node::<Arg>::empty_seq(), origin),
                data_def: primitives().never(),
            },
            origin,
        )
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

impl fmt::Display for UnsafeTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unsafe {}", self.inner)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Tuple(tuple_term) => write!(f, "{}", tuple_term),
            Term::Lit(lit) => write!(f, "{}", *lit.value()),
            Term::Ctor(ctor_term) => write!(f, "{}", ctor_term),
            Term::Call(fn_call_term) => write!(f, "{}", fn_call_term),
            Term::Fn(fn_def_id) => write!(
                f,
                "{}",
                if fn_def_id.map(|fn_def| fn_def.name.map(|sym| sym.name.is_none())) {
                    (*fn_def_id).to_string()
                } else {
                    (fn_def_id.map(|def| def.name)).to_string()
                }
            ),
            Term::Block(block_term) => write!(f, "{}", block_term),
            Term::Var(resolved_var) => write!(f, "{}", *resolved_var),
            Term::Loop(loop_term) => write!(f, "{}", loop_term),
            Term::LoopControl(loop_control_term) => {
                write!(f, "{}", loop_control_term)
            }
            Term::Match(match_term) => write!(f, "{}", match_term),
            Term::Return(return_term) => write!(f, "{}", return_term),
            Term::Decl(decl_stack_member_term) => {
                write!(f, "{}", decl_stack_member_term)
            }
            Term::Assign(assign_term) => write!(f, "{}", assign_term),
            Term::Unsafe(unsafe_term) => write!(f, "{}", unsafe_term),
            Term::Access(access_term) => write!(f, "{}", access_term),
            Term::Cast(cast_term) => write!(f, "{}", cast_term),
            Term::TypeOf(type_of_term) => write!(f, "{}", type_of_term),
            Term::Ref(ref_term) => write!(f, "{}", ref_term),
            Term::Deref(deref_term) => write!(f, "{}", deref_term),
            Term::Hole(hole) => write!(f, "{}", *hole),
            Term::Index(index) => {
                write!(f, "{}", index)
            }
            Term::Array(array) => {
                write!(f, "{}", array)
            }
            Ty::TupleTy(tuple_ty) => write!(f, "{}", tuple_ty),
            Ty::FnTy(fn_ty) => write!(f, "{}", fn_ty),
            Ty::RefTy(ref_ty) => write!(f, "{}", ref_ty),
            Ty::DataTy(data_ty) => write!(f, "{}", data_ty),
            Ty::Universe => write!(f, "Type"),
        }
    }
}

impl fmt::Display for TermId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", *self.value())
    }
}

impl fmt::Display for TermListId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, term) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", term)?;
        }
        Ok(())
    }
}

impl fmt::Display for TyOfTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "typeof {}", self.term)
    }
}
