use crate::new::{
    data::CtorDefId, mods::ModMemberId, scopes::StackMemberId, symbols::Symbol, trts::TrtMemberId,
};

/// A variable by name, which will be resolved to a more concrete variable term.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SymbolicVarTerm {
    pub name: Symbol,
}

/// A bound variable, originating from some bound.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct BoundVar {
    pub name: Symbol,
    // @@Todo: do we add more info here?
}

/// A variable resolved to some item
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ResolvedVarTerm {
    /// A stack variable
    StackVar(StackMemberId),
    /// A module member
    ModMember(ModMemberId),
    /// A trait member
    TrtMember(TrtMemberId),
    /// A constructor
    Ctor(CtorDefId),
    /// A bound variable
    BoundVar(BoundVar),
}
