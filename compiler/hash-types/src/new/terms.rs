//! Definitions related to terms.

use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{DefaultSequenceStore, DefaultStore},
};

use super::{
    casting::{CastTerm, CoerceTerm},
    environment::context::Binding,
    holes::HoleId,
    lits::LitTerm,
    symbols::Symbol,
    tys::TypeOfTerm,
};
use crate::new::{
    access::AccessTerm,
    control::{LoopControlTerm, LoopTerm, MatchTerm, ReturnTerm},
    data::{CtorTerm, DataDefId},
    fns::{FnCallTerm, FnDefId},
    mods::ModDefId,
    refs::{DerefTerm, RefTerm},
    scopes::{AssignTerm, BlockTerm, DeclStackMemberTerm},
    trts::TrtDefId,
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
    FnDef(FnDefId),

    // Scopes
    Block(BlockTerm),

    // Definitions
    TrtDef(TrtDefId),
    DataDef(DataDefId),
    ModDef(ModDefId),

    // Variables
    Var(Symbol),
    ResolvedVar(Binding),

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
    Coerce(CoerceTerm),

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
