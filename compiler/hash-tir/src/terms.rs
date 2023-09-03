//! Definitions related to terms.

use core::fmt;
use std::fmt::Debug;

use hash_ast::ast;
use hash_storage::store::{
    statics::{SequenceStoreValue, SingleStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_utils::derive_more::From;

use super::{casting::CastTerm, holes::Hole, symbols::SymbolId, tys::TypeOfTerm};
use crate::{
    access::AccessTerm,
    args::Arg,
    arrays::{ArrayTerm, IndexTerm},
    ast_info::HasNodeId,
    control::{LoopControlTerm, LoopTerm, MatchTerm, ReturnTerm},
    data::CtorTerm,
    environment::stores::tir_stores,
    fns::{FnCallTerm, FnDefId},
    lits::LitId,
    node::{Node, NodeOrigin},
    refs::{DerefTerm, RefTerm},
    scopes::{AssignTerm, BlockTerm, DeclTerm},
    tir_node_sequence_store_indirect, tir_node_single_store,
    tuples::TupleTerm,
    tys::{Ty, TyId},
    utils::common::get_location,
};

/// A term that can contain unsafe operations.
#[derive(Debug, Clone, Copy)]
pub struct UnsafeTerm {
    pub inner: TermId,
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
    // Primitives
    Tuple(TupleTerm),
    Lit(LitId),

    // Constructors
    Ctor(CtorTerm),

    // Functions
    FnCall(FnCallTerm),
    FnRef(FnDefId),

    // Scopes
    Block(BlockTerm),

    // Variables
    Var(SymbolId),

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

    // Types
    TypeOf(TypeOfTerm),
    Ty(TyId),

    // References
    Ref(RefTerm),
    Deref(DerefTerm),

    /// Holes
    Hole(Hole),
}

tir_node_single_store!(Term);
tir_node_sequence_store_indirect!(TermList[TermId]);

impl HasNodeId for TermId {
    fn node_id(&self) -> Option<ast::AstNodeId> {
        tir_stores().ast_info().terms().get_node_by_data(*self)
    }
}

impl Term {
    pub fn is_void(&self) -> bool {
        matches!(self, Term::Tuple(tuple_term) if tuple_term.data.value().is_empty())
    }

    pub fn void(origin: NodeOrigin) -> TermId {
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

    /// Create a new term.
    ///
    /// Prefer this to `Term::create` because this will also add the location
    /// and AST info to the term.
    ///
    /// @@Todo: remove once location store is removed.
    pub fn from(term: impl Into<Term>, origin: NodeOrigin) -> TermId {
        let term = term.into();
        let (ast_info, location) = match term {
            Term::Ty(ty) => (ty.node_id(), get_location(ty)),
            Term::FnRef(f) => (f.node_id(), get_location(f)),
            Term::Var(v) => (None, get_location(v)),
            _ => (None, None),
        };
        let created = Node::create_at(term, origin);
        if let Some(location) = location {
            tir_stores().location().add_location_to_target(created, location);
        }
        if let Some(ast_info) = ast_info {
            tir_stores().ast_info().terms().insert(ast_info, created);
        }
        created
    }

    /// Create a new term that inherits location and AST info from the given
    /// `source`.
    pub fn inherited_from(source: TermId, term: impl Into<Term>) -> TermId {
        let created = Self::from(term, source.origin());
        tir_stores().location().copy_location(source, created);
        if let Some(ast_info) = source.node_id() {
            tir_stores().ast_info().terms().insert(ast_info, created);
        }
        created
    }
}

impl TermId {
    /// Try to use the given term as a type, or defer to a `Ty::Eval`.
    pub fn as_ty(&self) -> TyId {
        match self.try_as_ty() {
            Some(ty) => ty,
            None => Ty::from(Ty::Eval(*self), self.origin()),
        }
    }

    /// Try to use the given term as a type if easily possible.
    pub fn try_as_ty(&self) -> Option<TyId> {
        match *self.value() {
            Term::Var(var) => Some(Ty::from(var, self.origin())),
            Term::Ty(ty) => Some(ty),
            Term::Hole(hole) => Some(Ty::from(hole, self.origin())),
            _ => None,
        }
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
            Term::FnCall(fn_call_term) => write!(f, "{}", fn_call_term),
            Term::FnRef(fn_def_id) => write!(
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
            Term::Ty(ty) => write!(f, "type {}", *ty),
            Term::Ref(ref_term) => write!(f, "{}", ref_term),
            Term::Deref(deref_term) => write!(f, "{}", deref_term),
            Term::Hole(hole) => write!(f, "{}", *hole),
            Term::Index(index) => {
                write!(f, "{}", index)
            }
            Term::Array(array) => {
                write!(f, "{}", array)
            }
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
