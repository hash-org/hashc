//! Contains structures that store information about the scopes in a given module, as well as the
//! symbols in each scope.
use super::primitives::TyId;
use hash_ast::ident::Identifier;
use std::collections::HashMap;

/// Represents a scope `{...}`. Contains a mapping for symbols within that scope and their targets.
#[derive(Debug, Default, Clone)]
pub struct Scope {
    symbols: HashMap<Identifier, TyId>,
}

impl Scope {
    pub fn new() -> Self {
        Self::default()
    }

    /// Resolve the given symbol into a [TyId].
    pub fn resolve_symbol(&self, symbol: Identifier) -> Option<TyId> {
        self.symbols.get(&symbol).copied()
    }

    /// Add the given symbol to the scope, for the given target.
    pub fn add_symbol(&mut self, symbol: Identifier, symbol_type: TyId) {
        self.symbols.insert(symbol, symbol_type);
    }
}

/// Represents a nested set of scopes.
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
            scopes: vec![Scope::new()],
        }
    }

    /// Create a [ScopeStack] from the given iterator of scopes.
    pub fn with_scopes(scopes: impl Iterator<Item = Scope>) -> Self {
        let mut stack = Self::empty();
        stack.scopes.extend(scopes);
        stack
    }

    /// Resolve a single symbol within the scope stack.
    pub fn resolve_symbol(&self, symbol: Identifier) -> Option<TyId> {
        for scope in self.iter_up() {
            if let Some(symbol_type) = scope.resolve_symbol(symbol) {
                return Some(symbol_type);
            }
        }

        None
    }

    /// Append a scope to the stack.
    pub fn append(&mut self, other: ScopeStack) {
        self.scopes.extend(other.scopes);
    }

    /// Add a symbol to the current scope in the stack.
    pub fn add_symbol(&mut self, symbol: Identifier, symbol_type: TyId) {
        self.current_scope_mut().add_symbol(symbol, symbol_type);
    }

    /// Get the current scope.
    pub fn current_scope(&self) -> &Scope {
        self.scopes.last().unwrap()
    }

    /// Get the current scope (mutable).
    pub fn current_scope_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }

    /// Enter a new empty scope.
    pub fn enter_scope(&mut self) {
        self.scopes.push(Scope::new());
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
