use hash_ast::{ident::Identifier, ast::TypeId};
use std::collections::HashMap;

use crate::types::{Types, TypeValue};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolType {
    Variable(TypeId),
    Type(TypeId),
}

#[derive(Debug, Default)]
pub struct Scope {
    symbols: HashMap<Identifier, SymbolType>,
}

impl Scope {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn resolve_symbol(&self, symbol: Identifier) -> Option<SymbolType> {
        self.symbols.get(&symbol).map(|&s| s)
    }

    pub fn add_symbol(&mut self, symbol: Identifier, symbol_type: SymbolType) {
        // @@TODO: naming clashes
        self.symbols.insert(symbol, symbol_type);
    }
}

#[derive(Debug)]
pub struct ScopeStack {
    scopes: Vec<Scope>,
}

impl Default for ScopeStack {
    fn default() -> Self {
        Self {
            scopes: vec![Scope::new()],
        }
    }
}

impl ScopeStack {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn resolve_symbol(&self, symbol: Identifier) -> Option<SymbolType> {
        for scope in self.iter_up() {
            if let Some(symbol_type) = scope.resolve_symbol(symbol) {
                return Some(symbol_type);
            }
        }

        None
    }

    pub fn add_symbol(&mut self, symbol: Identifier, symbol_type: SymbolType) {
        self.current_scope_mut().add_symbol(symbol, symbol_type);
    }

    pub fn current_scope(&self) -> &Scope {
        self.scopes.last().unwrap()
    }

    pub fn extract_current_scope(&mut self) -> Scope {
        self.scopes.pop().unwrap()
    }

    pub fn current_scope_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }

    pub fn enter_scope(&mut self) {
        self.scopes.push(Scope::new());
    }

    pub fn iter_up(&self) -> impl Iterator<Item = &Scope> {
        self.scopes.iter().rev()
    }

    pub fn iter_up_mut(&mut self) -> impl Iterator<Item = &mut Scope> {
        self.scopes.iter_mut().rev()
    }

    pub fn pop_scope(&mut self) -> Scope {
        match self.scopes.pop() {
            Some(scope) => scope,
            None => panic!("Cannot pop root scope"),
        }
    }
}

pub fn resolve_compound_symbol(
    scopes: &ScopeStack,
    types: &Types,
    symbols: &[Identifier],
) -> Option<SymbolType> {
    let mut last_scope = scopes.current_scope();
    let mut symbols_iter = symbols.iter().peekable();

    loop {
        match last_scope.resolve_symbol(*symbols_iter.next().unwrap()) {
            Some(symbol_ty @ SymbolType::Variable(type_id)) => match types.get(type_id) {
                TypeValue::Namespace(namespace_ty) => match symbols_iter.peek() {
                    Some(_) => {
                        last_scope = &namespace_ty.members;
                        continue;
                    }
                    None => {
                        return Some(symbol_ty);
                    }
                },
                _ => {}
            },
            Some(symbol_ty) => match symbols_iter.peek() {
                Some(_) => {
                    // @@Todo: error properly
                    panic!("Found trying to namespace type.");
                }
                None => {
                    return Some(symbol_ty);
                }
            },
            None => continue,
        }
    }
}
