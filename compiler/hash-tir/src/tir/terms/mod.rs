//! Definitions related to terms.

use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_storage::store::{
    SequenceStoreKey, TrivialSequenceStoreKey,
    statics::{SequenceStoreValue, SingleStoreValue, StoreId},
};

use crate::{
    intrinsics::definitions::Intrinsic,
    stores::tir_stores,
    tir::{
        Arg, ArgsId, CtorTerm, DataDefId, DataTy, LitId, Node, NodeId, NodeOrigin, Param, SymbolId,
    },
    tir_node_sequence_store_indirect, tir_node_single_store,
    visitor::Atom,
};

pub mod access;
pub mod annotation;
pub mod arrays;
pub mod blocks;
pub mod commands;
pub mod control;
pub mod fns;
pub mod holes;
pub mod refs;
pub mod tuples;

pub use access::*;
pub use annotation::*;
pub use arrays::*;
pub use blocks::*;
pub use commands::*;
pub use control::*;
pub use fns::*;
pub use holes::*;
pub use refs::*;
pub use tuples::*;

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

/// The type representing the universe.
///
/// Every other type is typed by this type.
#[derive(Debug, Clone, Copy)]
pub struct UniverseTy;

/// A variable, which is a symbol.
#[derive(Debug, Clone, Copy)]
pub struct VarTerm {
    pub symbol: SymbolId,
}

impl From<VarTerm> for SymbolId {
    fn from(var: VarTerm) -> Self {
        var.symbol
    }
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
    Var(VarTerm),

    // Blocks
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

    // Assignments
    Assign(AssignTerm),

    // Unsafe
    Unsafe(UnsafeTerm),

    // Access and indexing
    Access(AccessTerm),

    // Arrays
    Array(ArrayTerm),
    Index(IndexTerm),

    // Casting
    Annot(AnnotTerm),
    TyOf(TyOfTerm),

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
    Universe(UniverseTy),

    /// Holes
    Hole(Hole),

    /// Intrinsics
    Intrinsic(Intrinsic),
}

tir_node_single_store!(Term);
tir_node_sequence_store_indirect!(TermList[TermId]);

pub type Ty = Term;
pub type TyId = TermId;
pub type TyListId = TermListId;

/// Assert that the given term is of the given variant, and return it.
#[macro_export]
macro_rules! term_as_variant {
    ($self:expr, $term:expr, $variant:ident) => {{
        let term = $term;
        if let $crate::tir::Term::$variant(term) = *term {
            term
        } else {
            panic!("Expected term {} to be a {}", term, stringify!($variant))
        }
    }};
}

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
        Node::create(Node::at(Term::Var(VarTerm { symbol }), symbol.origin()))
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
        Node::create(Node::at(Ty::Universe(UniverseTy), origin))
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
    pub fn indexed_data_ty(data_def: DataDefId, args: ArgsId, origin: NodeOrigin) -> TyId {
        Node::create(Node::at(Ty::DataTy(DataTy { data_def, args }), origin))
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

    /// Create a new reference type.
    pub fn ref_ty(ty: TyId, kind: RefKind, mutable: bool, origin: NodeOrigin) -> TyId {
        Ty::from(RefTy { ty, kind, mutable }, origin)
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

impl From<SymbolId> for Term {
    fn from(symbol: SymbolId) -> Self {
        Term::Var(VarTerm { symbol })
    }
}

impl fmt::Display for UnsafeTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unsafe {}", self.inner)
    }
}

impl fmt::Display for VarTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.symbol)
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
            Term::Var(resolved_var) => write!(f, "{}", resolved_var),
            Term::Loop(loop_term) => write!(f, "{}", loop_term),
            Term::LoopControl(loop_control_term) => {
                write!(f, "{}", loop_control_term)
            }
            Term::Match(match_term) => write!(f, "{}", match_term),
            Term::Return(return_term) => write!(f, "{}", return_term),
            Term::Assign(assign_term) => write!(f, "{}", assign_term),
            Term::Unsafe(unsafe_term) => write!(f, "{}", unsafe_term),
            Term::Access(access_term) => write!(f, "{}", access_term),
            Term::Annot(cast_term) => write!(f, "{}", cast_term),
            Term::TyOf(type_of_term) => write!(f, "{}", type_of_term),
            Term::Ref(ref_term) => write!(f, "{}", ref_term),
            Term::Deref(deref_term) => write!(f, "{}", deref_term),
            Term::Hole(hole) => write!(f, "{}", *hole),
            Term::Index(index) => {
                write!(f, "{}", index)
            }
            Term::Array(array) => {
                write!(f, "{}", array)
            }
            Term::Intrinsic(intrinsic) => {
                write!(f, "{}", intrinsic)
            }
            Ty::TupleTy(tuple_ty) => write!(f, "{}", tuple_ty),
            Ty::FnTy(fn_ty) => write!(f, "{}", fn_ty),
            Ty::RefTy(ref_ty) => write!(f, "{}", ref_ty),
            Ty::DataTy(data_ty) => write!(f, "{}", data_ty),
            Ty::Universe(universe) => write!(f, "{}", universe),
        }
    }
}

impl fmt::Display for UniverseTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Type")
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
