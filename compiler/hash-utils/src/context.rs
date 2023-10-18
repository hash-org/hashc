//! An implementation of a two-level context using de-Bruijn levels.
//!
//! The context is a stack of scopes. Each scope is a list of members.
//! Each member has a symbol and a value. The symbol need not be unique
//! across scopes, but the value must be unique within a scope.
//!
//! Names are references into a context which include a scope index
//! and a member index.
//!
//! The context is parameterized by three types:
//! - `ScopeKind`: The type of the scope kind. This is used to distinguish
//!  different kinds of scopes, e.g. a module scope vs. a function scope.
//! - `Value`: The type of the value associated with each member.
//! - `Symbol`: The type of the symbol associated with each member.
//! These types are collected into a `ContextTypes` trait, which is then
//! used as a bound on all relevant structures.
use std::{
    fmt::Debug,
    hash::{Hash, Hasher},
};

use thin_vec::ThinVec;

/// A collection of types which this module is parameterised over.
pub trait ContextTypes {
    /// The type of the scope kind. This is used to distinguish different kinds
    /// of scopes, e.g. a module scope vs. a function scope.
    type ScopeKind: Debug + Clone;
    /// The type of the value associated with each member.
    type Value: Debug + Clone;
    /// The type of the symbol associated with each member.
    type Symbol: Debug + PartialEq + Eq + Copy;
}

/// An index into a context, pointing to a scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ScopeIndex {
    data: u32,
}

/// An index into a scope, pointing to a member.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MemberIndex {
    data: u32,
}

/// A name in a context, which is a reference to a member.
///
/// The name includes the symbol of the member.
///
/// *Warning*: Comparisons and hashing of `Name` are only performed on the
/// scope index and member index, not the symbol.
#[derive(Debug, Clone, Copy)]
pub struct Name<C: ContextTypes> {
    /// The symbolic name of the member.
    pub symbol: C::Symbol,
    /// The index of the scope containing the member.
    pub scope_index: ScopeIndex,
    /// The index of the member within the scope.
    pub member_index: MemberIndex,
}

// Implementations of `Hash`, `PartialEq`, `Eq`, and `PartialOrd` for
// the scope index and member index of `Name`:

impl<C: ContextTypes> Hash for Name<C> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.scope_index.hash(state);
        self.member_index.hash(state);
    }
}

impl<C: ContextTypes> PartialEq for Name<C> {
    fn eq(&self, other: &Self) -> bool {
        self.scope_index == other.scope_index && self.member_index == other.member_index
    }
}

impl<C: ContextTypes> Eq for Name<C> {}

impl<C: ContextTypes> PartialOrd for Name<C> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<C: ContextTypes> Ord for Name<C> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.scope_index.cmp(&other.scope_index) {
            core::cmp::Ordering::Equal => {}
            ord => return ord,
        }
        self.member_index.cmp(&other.member_index)
    }
}

/// A member in a scope, which consists of a symbol and a value.
#[derive(Debug, Clone, Copy)]
pub struct Member<C: ContextTypes> {
    /// The symbolic name of the member.
    pub symbol: C::Symbol,
    /// The value of the member.
    pub value: C::Value,
}

/// A scope in a context, which consists of a kind and a list of members.
///
/// The kind of the scope is some extra information about the scope, e.g.
/// whether it is a module scope or a function scope.
///
/// All operations on the scope are constant-time unless otherwise specified.
#[derive(Debug, Clone)]
pub struct Scope<C: ContextTypes> {
    kind: C::ScopeKind,
    members: ThinVec<Member<C>>,
}

impl<C: ContextTypes> Scope<C> {
    /// Create a new empty scope with the given kind.
    pub fn empty(kind: C::ScopeKind) -> Self {
        Self { kind, members: ThinVec::new() }
    }

    /// Get the kind of the scope.
    pub fn kind(&self) -> &C::ScopeKind {
        &self.kind
    }

    /// Whether the scope contains the given member index.
    pub fn has_member_index(&self, index: MemberIndex) -> bool {
        index.data < self.members.len() as u32
    }

    /// Get the member at the given index, if it exists.
    pub fn get_member(&self, index: MemberIndex) -> Option<&Member<C>> {
        self.members.get(index.data as usize)
    }

    /// Get the member at the given index, if it exists (mutable).
    pub fn get_member_mut(&mut self, index: MemberIndex) -> Option<&mut Member<C>> {
        self.members.get_mut(index.data as usize)
    }

    /// Search for a member with the given symbol, returning its index if it
    /// exists.
    ///
    /// This has a linear time complexity.
    pub fn search_member(&self, symbol: C::Symbol) -> Option<MemberIndex> {
        self.members
            .iter()
            .enumerate()
            .find(|(_, member)| member.symbol == symbol)
            .map(|(index, _)| MemberIndex { data: index as u32 })
    }

    /// Push a new member onto the scope, returning its index.
    ///
    /// The index of the member will be one greater than the previous index.
    pub fn push_member(&mut self, member: Member<C>) -> MemberIndex {
        let index = MemberIndex { data: self.members.len() as u32 };
        self.members.push(member);
        index
    }
}

/// A context, which is a stack of scopes of members.
///
/// All operations on the context are constant-time unless otherwise specified.
#[derive(Debug, Clone)]
pub struct Context<C: ContextTypes> {
    scopes: ThinVec<Scope<C>>,
}

impl<C: ContextTypes> Context<C> {
    /// Create a new empty context.
    pub fn empty() -> Self {
        Self { scopes: ThinVec::new() }
    }

    /// Get the current scope index, if it exists.
    ///
    /// This will be the *highest* scope index, i.e. the most recently pushed.
    pub fn get_current_scope_index(&self) -> Option<ScopeIndex> {
        match self.scopes.len() {
            0 => None,
            len => Some(ScopeIndex { data: (len - 1) as u32 }),
        }
    }

    /// Get the current scope, if it exists.
    pub fn get_current_scope(&self) -> Option<&Scope<C>> {
        self.scopes.last()
    }

    /// Get the current scope, if it exists (mutable).
    pub fn get_current_scope_mut(&mut self) -> Option<&mut Scope<C>> {
        self.scopes.last_mut()
    }

    /// Get the scope at the given index, if it exists.
    pub fn get_scope(&self, index: ScopeIndex) -> Option<&Scope<C>> {
        self.scopes.get(index.data as usize)
    }

    /// Get the scope at the given index, if it exists (mutable).
    pub fn get_scope_mut(&mut self, index: ScopeIndex) -> Option<&mut Scope<C>> {
        self.scopes.get_mut(index.data as usize)
    }

    /// Get the member at the given name, if it exists.
    pub fn get_member(&self, name: Name<C>) -> Option<&Member<C>> {
        let scope = self.scopes.get(name.scope_index.data as usize)?;
        scope.get_member(name.member_index)
    }

    /// Get the member at the given name, if it exists (mutable).
    pub fn get_member_mut(&mut self, name: Name<C>) -> Option<&mut Member<C>> {
        let scope = self.scopes.get_mut(name.scope_index.data as usize)?;
        scope.get_member_mut(name.member_index)
    }

    /// Whether the context contains the given scope index.
    pub fn has_scope_index(&self, index: ScopeIndex) -> bool {
        index.data < self.scopes.len() as u32
    }

    /// Search for a member with the given symbol, returning its name if it
    /// exists.
    ///
    /// This will search the scopes from highest to lowest, i.e. from the
    /// most recently pushed to the least recently pushed. Once a matching
    /// member is found, the search will stop.
    ///
    /// This has a linear time complexity proportional to the size of the
    /// context.
    pub fn search_member(&self, symbol: C::Symbol) -> Option<Name<C>> {
        self.scopes.iter().enumerate().find_map(|(scope_index, scope)| {
            scope.search_member(symbol).map(|member_index| Name {
                scope_index: ScopeIndex { data: scope_index as u32 },
                member_index,
                symbol,
            })
        })
    }

    /// Search for a member with the given symbol in the given scope, returning
    /// its name if it exists.
    ///
    /// *Warning*: The index of the given scope must be valid, i.e.
    /// `self.has_scope_index(index)`.
    ///
    /// This has a linear time complexity proportional to the size of the
    /// given scope.
    pub fn search_member_in(&self, index: ScopeIndex, name: C::Symbol) -> Option<Name<C>> {
        let scope = self.get_scope(index).expect("got an invalid scope index");
        scope.search_member(name).map(|member_index| Name {
            scope_index: index,
            member_index,
            symbol: name,
        })
    }

    /// Enter a new scope, running the given closure with the new scope.
    ///
    /// The new scope will be pushed onto the stack, and then popped off
    /// after the closure returns.
    ///
    /// The function will be passed a mutable reference to this context to get
    /// around mutability restrictions.
    ///
    /// Once the function returns, the scope will be popped off the stack and
    /// returned alongside any return value from the closure.
    pub fn enter_scope<T>(
        &mut self,
        scope: Scope<C>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> (T, Scope<C>) {
        self.scopes.push(scope);
        let result = f(self);
        let scope = self.scopes.pop().unwrap();
        (result, scope)
    }
}
