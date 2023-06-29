//! Definitions related to terms.

use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_utils::store::{SequenceStore, Store, TrivialSequenceStoreKey};

use super::{casting::CastTerm, holes::Hole, symbols::Symbol, tys::TypeOfTerm};
use crate::{
    access::AccessTerm,
    arrays::{ArrayTerm, IndexTerm},
    control::{LoopControlTerm, LoopTerm, MatchTerm, ReturnTerm},
    data::CtorTerm,
    fns::{FnCallTerm, FnDefId},
    lits::Lit,
    refs::{DerefTerm, RefTerm},
    scopes::{AssignTerm, BlockTerm, DeclTerm},
    tir_debug_value_of_single_store_id, tir_sequence_store_indirect, tir_single_store,
    tuples::TupleTerm,
    tys::TyId,
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
#[derive(Debug, Clone, Copy, From)]
pub enum Term {
    // Primitives
    Tuple(TupleTerm),
    Lit(Lit),

    // Constructors
    Ctor(CtorTerm),

    // Functions
    FnCall(FnCallTerm),
    FnRef(FnDefId),

    // Scopes
    Block(BlockTerm),

    // Variables
    Var(Symbol),

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

tir_single_store!(
    store = pub TermStore,
    id = pub TermId,
    value = Term,
    store_name = term
);

tir_debug_value_of_single_store_id!(TermId);

tir_sequence_store_indirect!(
    store = pub TermListStore,
    id = pub TermListId[TermId],
    store_name = term_list
);

impl fmt::Display for UnsafeTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unsafe {}", self.inner)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Tuple(tuple_term) => write!(f, "{}", (tuple_term)),
            Term::Lit(lit) => write!(f, "{}", *lit),
            Term::Ctor(ctor_term) => write!(f, "{}", (ctor_term)),
            Term::FnCall(fn_call_term) => write!(f, "{}", (fn_call_term)),
            Term::FnRef(fn_def_id) => write!(
                f,
                "{}",
                if fn_def_id.map(|fn_def| fn_def.name.map(|sym| sym.name.is_none())) {
                    (*fn_def_id).to_string()
                } else {
                    (fn_def_id.map(|def| def.name)).to_string()
                }
            ),
            Term::Block(block_term) => write!(f, "{}", (block_term)),
            Term::Var(resolved_var) => write!(f, "{}", (*resolved_var)),
            Term::Loop(loop_term) => write!(f, "{}", (loop_term)),
            Term::LoopControl(loop_control_term) => {
                write!(f, "{}", (loop_control_term))
            }
            Term::Match(match_term) => write!(f, "{}", (match_term)),
            Term::Return(return_term) => write!(f, "{}", (return_term)),
            Term::Decl(decl_stack_member_term) => {
                write!(f, "{}", (decl_stack_member_term))
            }
            Term::Assign(assign_term) => write!(f, "{}", (assign_term)),
            Term::Unsafe(unsafe_term) => write!(f, "{}", (unsafe_term)),
            Term::Access(access_term) => write!(f, "{}", (access_term)),
            Term::Cast(cast_term) => write!(f, "{}", (cast_term)),
            Term::TypeOf(type_of_term) => write!(f, "{}", (type_of_term)),
            Term::Ty(ty) => write!(f, "type {}", (*ty)),
            Term::Ref(ref_term) => write!(f, "{}", (ref_term)),
            Term::Deref(deref_term) => write!(f, "{}", (deref_term)),
            Term::Hole(hole) => write!(f, "{}", (*hole)),
            Term::Index(index) => {
                write!(f, "{}", (index))
            }
            Term::Array(array) => {
                write!(f, "{}", (array))
            }
        }
    }
}

impl fmt::Display for TermId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
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
