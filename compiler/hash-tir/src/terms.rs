//! Definitions related to terms.

use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_utils::store::{CloneStore, SequenceStore, Store};

use super::{
    casting::CastTerm,
    environment::env::{AccessToEnv, WithEnv},
    holes::Hole,
    symbols::Symbol,
    tys::TypeOfTerm,
};
use crate::{
    access::AccessTerm,
    arrays::{ArrayTerm, IndexTerm},
    control::{LoopControlTerm, LoopTerm, MatchTerm, ReturnTerm},
    data::CtorTerm,
    fns::{FnCallTerm, FnDefId},
    lits::Lit,
    refs::{DerefTerm, RefTerm},
    scopes::{AssignTerm, BlockTerm, DeclTerm},
    tir_sequence_store_indirect, tir_single_store,
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

tir_sequence_store_indirect!(
    store = pub TermListStore,
    id = pub TermListId[TermId],
    store_name = term_list
);

impl fmt::Display for WithEnv<'_, &UnsafeTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unsafe {}", self.env().with(self.value.inner))
    }
}

impl fmt::Display for WithEnv<'_, &Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            Term::Tuple(tuple_term) => write!(f, "{}", self.env().with(tuple_term)),
            Term::Lit(lit) => write!(f, "{}", *lit),
            Term::Ctor(ctor_term) => write!(f, "{}", self.env().with(ctor_term)),
            Term::FnCall(fn_call_term) => write!(f, "{}", self.env().with(fn_call_term)),
            Term::FnRef(fn_def_id) => write!(
                f,
                "{}",
                self.stores().fn_def().map_fast(*fn_def_id, |fn_def| {
                    if self.stores().symbol().map_fast(fn_def.name, |sym| sym.name).is_none() {
                        self.env().with(*fn_def_id).to_string()
                    } else {
                        self.env().with(fn_def.name).to_string()
                    }
                })
            ),
            Term::Block(block_term) => write!(f, "{}", self.env().with(block_term)),
            Term::Var(resolved_var) => write!(f, "{}", self.env().with(*resolved_var)),
            Term::Loop(loop_term) => write!(f, "{}", self.env().with(loop_term)),
            Term::LoopControl(loop_control_term) => {
                write!(f, "{}", self.env().with(loop_control_term))
            }
            Term::Match(match_term) => write!(f, "{}", self.env().with(match_term)),
            Term::Return(return_term) => write!(f, "{}", self.env().with(return_term)),
            Term::Decl(decl_stack_member_term) => {
                write!(f, "{}", self.env().with(decl_stack_member_term))
            }
            Term::Assign(assign_term) => write!(f, "{}", self.env().with(assign_term)),
            Term::Unsafe(unsafe_term) => write!(f, "{}", self.env().with(unsafe_term)),
            Term::Access(access_term) => write!(f, "{}", self.env().with(access_term)),
            Term::Cast(cast_term) => write!(f, "{}", self.env().with(cast_term)),
            Term::TypeOf(type_of_term) => write!(f, "{}", self.env().with(type_of_term)),
            Term::Ty(ty) => write!(f, "type {}", self.env().with(*ty)),
            Term::Ref(ref_term) => write!(f, "{}", self.env().with(ref_term)),
            Term::Deref(deref_term) => write!(f, "{}", self.env().with(deref_term)),
            Term::Hole(hole) => write!(f, "{}", self.env().with(*hole)),
            Term::Index(index) => {
                write!(f, "{}", self.env().with(index))
            }
            Term::Array(array) => {
                write!(f, "{}", self.env().with(array))
            }
        }
    }
}

impl fmt::Display for WithEnv<'_, TermId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.env().with(&self.env().stores().term().get(self.value)))
    }
}

impl fmt::Display for WithEnv<'_, TermListId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().term_list().map_fast(self.value, |list| {
            for (i, term) in list.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", self.env().with(*term))?;
            }
            Ok(())
        })
    }
}

impl fmt::Debug for WithEnv<'_, TermId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.env().stores().term().get(self.value))
    }
}
