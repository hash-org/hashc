//! Representing and modifying the typechecking context.
use std::cell::RefCell;

use hash_types::new::{
    data::CtorDefId, mods::ModMemberId, params::ParamTarget, scopes::StackMemberId,
    symbols::Symbol, trts::TrtMemberId, tys::TyId,
};
use indexmap::IndexMap;

/// A bound variable, originating from some bound.
#[derive(Debug, Copy, Clone)]
pub struct BoundVar {
    /// The name/position of the bound variable.
    pub name: Symbol,
    /// The type of the bound variable.
    pub ty: TyId,
    /// The target of the bound variable.
    pub target: ParamTarget,
}

/// The kind of a binding.
#[derive(Debug, Clone, Copy)]
pub enum BindingKind {
    /// A binding that is a trait member.
    ///
    /// For example, `trait { y := 3; z := y }`
    TrtMember(TrtMemberId),
    /// A binding that is a module member.
    ///
    /// For example, `mod { Q := struct(); Q }`
    ModMember(ModMemberId),
    /// A binding that is a stack member.
    ///
    /// For example, `{ a := 3; a }`
    StackMember(StackMemberId),
    /// A binding that is a constructor definition.
    ///
    /// For example, `false`, `None`, `Some(_)`.
    Ctor(CtorDefId),
    /// A binding that represents a parameter variable of a function.
    ///
    /// For example, `(x: i32) => x`
    BoundVar(BoundVar),
}

/// A binding.
///
/// A binding is essentially something in the form `a := b` in the current
/// context.
#[derive(Debug, Clone, Copy)]
pub struct Binding {
    /// The name of the binding.
    pub name: Symbol,
    /// The kind of the binding.
    pub kind: BindingKind,
}

/// Data structure managing the typechecking context.
///
/// The context is a stack of scopes, each scope being a stack in itself.
///
/// The context is used to resolve symbols to their corresponding bindings, and
/// thus interpret their meaning. It can read and add [`Binding`]s, and can
/// enter and exit scopes.
#[derive(Debug, Clone)]
pub struct Context {
    scope_levels: RefCell<Vec<usize>>,
    members: RefCell<IndexMap<Symbol, Binding>>,
}

impl Context {
    pub fn new() -> Self {
        Self { scope_levels: RefCell::new(vec![]), members: RefCell::new(IndexMap::new()) }
    }

    /// Enter a new scope in the context.
    pub fn add_scope(&self) {
        self.scope_levels.borrow_mut().push(self.members.borrow().len());
    }

    /// Exit the last entered scope in the context
    ///
    /// Returns true if the scope was removed, or false if there are no scopes
    /// to remove.
    pub fn remove_scope(&self) -> bool {
        match self.scope_levels.borrow_mut().pop() {
            Some(last_level) => {
                self.members.borrow_mut().truncate(last_level);
                true
            }
            None => false,
        }
    }

    /// Enter a new scope in the context, and run the given function in that
    /// scope.
    ///
    /// The scope is exited after the function has been run.
    pub fn enter_scope<T>(&self, f: impl FnOnce() -> T) -> T {
        self.add_scope();
        let res = f();
        if !self.remove_scope() {
            panic!("Context::enter_scope: tried to remove a scope that didn't exist");
        }
        res
    }

    /// Add a new binding to the current scope context.
    pub fn add_binding(&mut self, binding: Binding) {
        self.members.borrow_mut().insert(binding.name, binding);
    }

    /// Get a binding from the context, reading all accessible scopes.
    pub fn get_binding(&self, name: Symbol) -> Option<Binding> {
        self.members.borrow().get(&name).copied()
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}
