use std::cell::RefCell;

use indexmap::IndexMap;

use super::{
    data::CtorDefId, mods::ModMemberId, scopes::StackMemberId, symbols::Symbol, trts::TrtMemberId,
    tys::TyId,
};

/// A bound variable, originating from some bound.
#[derive(Debug, Copy, Clone)]
pub struct BoundVar {
    pub name: Symbol,
    pub ty: TyId,
    // @@Todo: do we add more info here?
}

#[derive(Debug, Clone, Copy)]
pub enum BindingKind {
    TrtMember(TrtMemberId),
    ModMember(ModMemberId),
    StackMember(StackMemberId),
    Ctor(CtorDefId),
    BoundVar(BoundVar),
}

#[derive(Debug, Clone, Copy)]
pub struct Binding {
    pub name: Symbol,
    pub kind: BindingKind,
}

#[derive(Debug, Clone)]
pub struct Context {
    scope_levels: RefCell<Vec<usize>>,
    members: RefCell<IndexMap<Symbol, Binding>>,
}

impl Context {
    pub fn new() -> Self {
        Self { scope_levels: RefCell::new(vec![]), members: RefCell::new(IndexMap::new()) }
    }

    pub fn add_scope(&self) {
        self.scope_levels.borrow_mut().push(self.members.borrow().len());
    }

    pub fn remove_scope(&self) {
        match self.scope_levels.borrow_mut().pop() {
            Some(last_level) => self.members.borrow_mut().truncate(last_level),
            None => panic!("Attempted to pop scope when no scopes are present"),
        }
    }

    pub fn enter_scope<T>(&self, f: impl FnOnce() -> T) -> T {
        self.add_scope();
        let res = f();
        self.remove_scope();
        res
    }

    pub fn add_binding(&mut self, binding: Binding) {
        self.members.borrow_mut().insert(binding.name, binding);
    }

    pub fn get_binding(&self, name: Symbol) -> Option<Binding> {
        self.members.borrow().get(&name).copied()
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}
