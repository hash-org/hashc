//! Definitions related to terms.

use core::fmt;
use std::fmt::Debug;

use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{CloneStore, DefaultSequenceStore, DefaultStore},
};

use super::{
    casting::CastTerm,
    environment::{
        context::Binding,
        env::{AccessToEnv, WithEnv},
    },
    holes::HoleId,
    lits::LitTerm,
    tys::TypeOfTerm,
};
use crate::new::{
    access::AccessTerm,
    control::{LoopControlTerm, LoopTerm, MatchTerm, ReturnTerm},
    data::CtorTerm,
    fns::{FnCallTerm, FnDefId},
    refs::{DerefTerm, RefTerm},
    scopes::{AssignTerm, BlockTerm, DeclStackMemberTerm},
    tuples::TupleTerm,
    tys::TyId,
    unions::UnionVariantTerm,
};

/// A term that can contain unsafe operations.
#[derive(Debug, Clone, Copy)]
pub struct UnsafeTerm {
    pub inner: TermId,
}

/// A term whose value is only known at runtime.
#[derive(Debug, Clone, Copy)]
pub struct RuntimeTerm {
    pub term_ty: TyId,
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
#[derive(Debug, Clone, Copy)]
pub enum Term {
    // Runtime
    Runtime(RuntimeTerm),

    // Primitives
    UnionVariant(UnionVariantTerm),
    Tuple(TupleTerm),
    Lit(LitTerm),

    // Constructors
    Ctor(CtorTerm),

    // Functions
    FnCall(FnCallTerm),
    // @@Todo: create separate closure type ~= (FnDefId, CapturedVars)
    Closure(FnDefId),

    // Scopes
    Block(BlockTerm),

    // Variables
    Var(Binding),

    // Loops
    Loop(LoopTerm),
    LoopControl(LoopControlTerm),

    // Control flow
    Match(MatchTerm),
    Return(ReturnTerm),

    // Declarations and assignments
    DeclStackMember(DeclStackMemberTerm),
    Assign(AssignTerm),

    // Unsafe
    Unsafe(UnsafeTerm),

    // Access
    Access(AccessTerm),

    // Casting
    Cast(CastTerm),

    // Types
    TypeOf(TypeOfTerm),
    Ty(TyId),

    // References
    Ref(RefTerm),
    Deref(DerefTerm),

    /// Term hole
    ///
    /// Invariant: `hole.kind == HoleKind::Term`
    // @@Reconsider: this invariant might need to be broken sometimes if types are used in expr
    // context.
    Hole(HoleId),
}

new_store_key!(pub TermId);
pub type TermStore = DefaultStore<TermId, Term>;

new_sequence_store_key!(pub TermListId);
pub type TermListStore = DefaultSequenceStore<TermListId, TermId>;

impl fmt::Display for WithEnv<'_, &RuntimeTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{value {}}}", self.env().with(self.value.term_ty))
    }
}

impl fmt::Display for WithEnv<'_, TermId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.env().with(&self.env().stores().term().get(self.value)))
    }
}

impl fmt::Display for WithEnv<'_, &Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            Term::Runtime(_) => todo!(),
            Term::UnionVariant(_) => todo!(),
            Term::Tuple(_) => todo!(),
            Term::Lit(_) => todo!(),
            Term::Ctor(_) => todo!(),
            Term::FnCall(_) => todo!(),
            Term::Closure(_) => todo!(),
            Term::Block(_) => todo!(),
            Term::Var(resolved_var) => write!(f, "{}", self.env().with(resolved_var.name)),
            Term::Loop(_) => todo!(),
            Term::LoopControl(_) => todo!(),
            Term::Match(_) => todo!(),
            Term::Return(_) => todo!(),
            Term::DeclStackMember(_) => todo!(),
            Term::Assign(_) => todo!(),
            Term::Unsafe(_) => todo!(),
            Term::Access(_) => todo!(),
            Term::Cast(_) => todo!(),
            Term::TypeOf(_) => todo!(),
            Term::Ty(_) => todo!(),
            Term::Ref(_) => todo!(),
            Term::Deref(_) => todo!(),
            Term::Hole(hole) => write!(f, "{}", self.env().with(*hole)),
        }
    }
}
