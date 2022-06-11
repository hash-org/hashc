//! Contains structures that store information about the scopes in a given module, as well as the
//! symbols in each scope.
use super::primitives::{Member, Members};
use hash_ast::ident::Identifier;

/// A scope is either a variable scope or a constant scope.
///
/// Examples of variable scopes are:
/// - Block expression scope
/// - Function parameter scope
///
/// Examples of const scopes are:
/// - The root scope
/// - Module block scope
/// - Trait block scope
/// - Impl block scope
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    Variable,
    Constant,
}

/// Represents a scope, which has a kind as well as a set of members.
///
/// If the kind is `Constant`, then all the members have:
/// - Any `visibility`
/// - `mutability = Immutable`
///
/// If the kind is `Variable`, then all members have:
/// - `visibility = Private`
/// - Any `mutability`
///
/// @@Future: Maybe we should store the origin of each scope in some place, for better error
/// messages.
#[derive(Debug, Clone)]
pub struct Scope {
    pub kind: ScopeKind,
    pub members: Members,
}

impl Scope {
    /// Create an empty [Scope], with no members, and the given [ScopeKind].
    pub fn empty(kind: ScopeKind) -> Self {
        Self {
            kind,
            members: Members::empty(),
        }
    }
}

/// Represents a "nested" set of scopes.
///
/// This is dynamically modified during typechecking when the checker enters (push) or exits (pop)
/// some scope.
#[derive(Debug, Clone)]
pub struct ScopeStack {
    scopes: Vec<Scope>,
}

impl ScopeStack {
    /// Create an empty [ScopeStack].
    pub fn empty() -> Self {
        Self {
            scopes: vec![Scope::empty(ScopeKind::Constant)],
        }
    }

    /// Create a [ScopeStack] from the given iterator of scopes.
    pub fn with_scopes(scopes: impl Iterator<Item = Scope>) -> Self {
        let mut stack = Self::empty();
        stack.scopes.extend(scopes);
        stack
    }

    /// Resolve a single symbol within the scope stack.
    pub fn resolve_symbol(&self, symbol: Identifier) -> Option<&Member> {
        for scope in self.iter_up() {
            if let Some(member) = scope.members.get(symbol) {
                return Some(member);
            }
        }

        None
    }

    /// Append a scope to the stack.
    pub fn append(&mut self, other: ScopeStack) {
        self.scopes.extend(other.scopes);
    }

    /// Get the current scope.
    pub fn current_scope(&self) -> &Scope {
        self.scopes.last().unwrap()
    }

    /// Get the current scope (mutable).
    pub fn current_scope_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }

    /// Enter a new empty scope of the given [ScopeKind].
    pub fn enter_scope(&mut self, kind: ScopeKind) {
        self.scopes.push(Scope::empty(kind));
    }

    /// Iterate up the scopes in the stack.
    pub fn iter_up(&self) -> impl Iterator<Item = &Scope> {
        self.scopes.iter().rev()
    }

    /// Iterate up the scopes in the stack (mutable).
    pub fn iter_up_mut(&mut self) -> impl Iterator<Item = &mut Scope> {
        self.scopes.iter_mut().rev()
    }

    /// Pop the current scope.
    pub fn pop_scope(&mut self) -> Scope {
        // Don't include the first element (root scope).
        if self.scopes.len() <= 1 {
            panic!("Cannot pop root scope")
        } else {
            self.scopes.pop().unwrap()
        }
    }
}
