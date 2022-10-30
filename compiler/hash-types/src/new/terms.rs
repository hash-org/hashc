//! Definitions related to terms.

use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{DefaultSequenceStore, DefaultStore},
};

use crate::new::{
    args::ArgsId,
    control::{LoopControlTerm, LoopTerm, MatchTerm, ReturnTerm},
    data::{CtorTerm, DataDefId},
    fns::{FnCallTerm, FnDefId},
    mods::ModDefId,
    refs::{DerefTerm, RefTerm},
    scopes::{AccessTerm, AssignTerm, BlockTerm, DeclStackMemberTerm},
    trts::TrtDefId,
    tuples::TupleTerm,
    types::TyId,
    unions::UnionVariantTerm,
    vars::{ResolvedVarTerm, SymbolicVarTerm},
};

/// A term that can contain unsafe operations.
#[derive(Debug, Clone, Copy)]
pub struct UnsafeTerm {
    pub inner: TermId,
}

/// Cast a given term to a given type.
#[derive(Debug, Clone, Copy)]
pub struct CastTerm {
    pub subject: TermId,
    pub ty: TyId,
}

/// Infer the type of the given term, returning its type.
#[derive(Debug, Clone, Copy)]
pub struct TypeOfTerm {
    pub term: TermId,
}

/// A term whose value is only known at runtime.
#[derive(Debug, Clone, Copy)]
pub struct RuntimeTerm {
    pub term_ty: TyId,
}

/// An application of a term to a list of arguments.
///
/// This is a term which will resolve to a function call, or a constructor call.
#[derive(Debug, Clone, Copy)]
pub struct AppTerm {
    pub subject: TermId,
    pub args: ArgsId,
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
    // Primitives
    Ty(TyId),
    Cast(CastTerm),
    Runtime(RuntimeTerm),
    UnionVariant(UnionVariantTerm),
    Tuple(TupleTerm),
    TypeOfTerm(TypeOfTerm),
    Ctor(CtorTerm),

    // To-be-resolved
    SymbolicVar(SymbolicVarTerm),
    App(AppTerm),

    // Functions
    FnCall(FnCallTerm),
    FnDef(FnDefId),

    // Scopes
    Access(AccessTerm),
    Block(BlockTerm),

    // Definitions
    TrtDef(TrtDefId),
    DataDef(DataDefId),
    ModDef(ModDefId),

    // Variables
    ResolvedVar(ResolvedVarTerm),

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

    // References
    Ref(RefTerm),
    Deref(DerefTerm),
}

new_store_key!(pub TermId);
pub type TermStore = DefaultStore<TermId, Term>;

new_sequence_store_key!(pub TermListId);
pub type TermListStore = DefaultSequenceStore<TermListId, TermId>;
