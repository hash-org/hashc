//! Representing and modifying the typechecking context.
use core::fmt;
use std::{
    cell::{Ref, RefCell},
    convert::Infallible,
    ops::Range,
};

use hash_storage::{
    get,
    store::{statics::StoreId, SequenceStoreKey, StoreKey, TrivialSequenceStoreKey},
};
use hash_utils::{
    derive_more::From, fxhash::FxBuildHasher, indexmap::IndexMap, itertools::Itertools,
};

use crate::{
    intrinsics::definitions::Intrinsic,
    stack::StackId,
    sub::Sub,
    tir::{
        ArgId, ArgsId, CtorDefId, DataDefId, FnDefId, FnTy, ModDefId, ParamId, ParamsId, SymbolId,
        TermId, TupleTy, TyId,
    },
};

/// A binding that contains a type and optional value.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum ContextMember {
    Typing { name: SymbolId, ty: TyId },
    Assignment { name: SymbolId, value: TermId },
}

impl ContextMember {
    pub fn name(&self) -> SymbolId {
        match self {
            ContextMember::Typing { name, .. } => *name,
            ContextMember::Assignment { name, .. } => *name,
        }
    }
}

/// All the different kinds of scope there are, and their associated data.
#[derive(Debug, Clone, Copy, From)]
pub enum ScopeKind {
    /// A module scope.
    Mod(ModDefId),
    // A stack scope.
    Stack(StackId),
    /// A function scope.
    Fn(FnDefId),
    /// An intrinsic scope.
    Intrinsic(Intrinsic),
    /// A data definition.
    Data(DataDefId),
    /// A constructor definition.
    Ctor(CtorDefId),
    /// A function type scope.
    FnTy(FnTy),
    /// A tuple type scope.
    TupleTy(TupleTy),
    /// A substitution scope.
    Sub,
}

/// Information about a scope in the context.
#[derive(Debug, Clone)]
pub struct Scope {
    /// The kind of the scope.
    kind: ScopeKind,
    /// The bindings of the scope
    decls: RefCell<IndexMap<SymbolId, ContextMember, FxBuildHasher>>,
}

impl Scope {
    /// Create a new scope with the given kind.
    pub fn with_empty_members(kind: ScopeKind) -> Self {
        Self { kind, decls: RefCell::new(IndexMap::default()) }
    }

    /// Add a binding to the scope.
    pub fn add_decl(&self, decl: ContextMember) {
        self.decls.borrow_mut().insert(decl.name(), decl);
    }

    /// Get the decl corresponding to the given symbol.
    pub fn get_decl(&self, symbol: SymbolId) -> Option<ContextMember> {
        self.decls.borrow().get(&symbol).copied()
    }

    /// Set an existing decl kind of the given symbol.
    ///
    /// Returns `true` if the decl was found and updated, `false` otherwise.
    pub fn set_existing_decl(
        &self,
        symbol: SymbolId,
        f: &impl Fn(ContextMember) -> ContextMember,
    ) -> bool {
        if let Some(old) = self.get_decl(symbol) {
            self.decls.borrow_mut().insert(symbol, f(old));
            true
        } else {
            false
        }
    }
}

/// Trait for types that have a context available to them.
pub trait HasContext {
    fn context(&self) -> &Context;
}

/// Trait for types that have a context mutable available to them.
pub trait HasContextMut {
    fn context_mut(&mut self) -> &mut Context;
}

/// Data structure managing the typechecking context.
///
/// The context is a stack of scopes, each scope being a stack in itself.
///
/// The context is used to resolve symbols to their corresponding decls, and
/// thus interpret their meaning. It can read and add [`Decl`]s, and can
/// enter and exit scopes.
#[derive(Debug, Clone, Default)]
pub struct Context {
    scopes: RefCell<Vec<Scope>>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    /// Enter a new scope in the context.
    pub fn add_scope(&self, kind: ScopeKind) {
        self.scopes.borrow_mut().push(Scope::with_empty_members(kind));
    }

    /// Exit the last entered scope in the context
    ///
    /// Returns the scope kind that was removed, or `None` if there are no
    /// scopes to remove.
    pub fn remove_scope(&self) -> Option<Scope> {
        self.scopes.borrow_mut().pop()
    }

    /// Enter a new scope in the context, and run the given function in that
    /// scope.
    ///
    /// The scope is exited after the function has been run.
    pub fn enter_scope<T>(&self, kind: ScopeKind, f: impl FnOnce() -> T) -> T {
        self.add_scope(kind);
        let res = f();
        if self.remove_scope().is_none() {
            panic!("tried to remove a scope that didn't exist");
        }
        res
    }

    /// Enter a new scope in the context, and run the given function in that
    /// scope, with a mutable `self` that implements [`AccessToEnv`].
    ///
    /// The scope is exited after the function has been run.
    pub fn enter_scope_mut<T, This: HasContext>(
        this: &mut This,
        kind: ScopeKind,
        f: impl FnOnce(&mut This) -> T,
    ) -> T {
        this.context().add_scope(kind);
        let res = f(this);
        if this.context().remove_scope().is_none() {
            panic!("tried to remove a scope that didn't exist");
        }
        res
    }

    /// Add a declaration to the current scope.
    pub fn add_decl(&self, decl: ContextMember) {
        self.get_current_scope_ref().add_decl(decl)
    }

    /// Modify a decl in the context, with a function that takes the current
    /// decl kind and returns the new decl kind.
    pub fn modify_decl_with(&self, name: SymbolId, f: impl Fn(ContextMember) -> ContextMember) {
        let _ = self
            .scopes
            .borrow()
            .iter()
            .rev()
            .find(|scope| scope.set_existing_decl(name, &f))
            .unwrap_or_else(|| panic!("tried to modify a decl that doesn't exist"));
    }

    /// Get a reference to the current scope.
    pub fn get_current_scope_ref(&self) -> Ref<Scope> {
        Ref::map(self.scopes.borrow(), |scopes| {
            scopes.last().unwrap_or_else(|| {
                panic!("tried to get the scope kind of a context with no scopes");
            })
        })
    }

    /// Get the current scope.
    pub fn get_current_scope_kind(&self) -> ScopeKind {
        self.get_current_scope_ref().kind
    }

    /// Get the closest stack scope and its index.
    pub fn get_closest_stack_scope_ref(&self) -> Ref<Scope> {
        Ref::map(self.scopes.borrow(), |scopes| {
            scopes
                .iter()
                .rev()
                .find(|scope| matches!(scope.kind, ScopeKind::Stack(_)))
                .unwrap_or_else(|| {
                    panic!("tried to get the scope kind of a context with no scopes");
                })
        })
    }

    pub fn get_scope_ref_at_index(&self, index: usize) -> Ref<Scope> {
        Ref::map(self.scopes.borrow(), |scopes| {
            scopes.get(index).unwrap_or_else(|| {
                panic!("tried to get the scope kind of a context with no scopes");
            })
        })
    }

    /// Get the index of the current scope.
    pub fn get_current_scope_index(&self) -> usize {
        self.scopes.borrow().len().checked_sub(1).unwrap_or_else(|| {
            panic!("tried to get the scope kind of a context with no scopes");
        })
    }

    /// Get information about the scope with the given index.
    pub fn get_scope(&self, index: usize) -> Ref<Scope> {
        Ref::map(self.scopes.borrow(), |scopes| &scopes[index])
    }

    /// Get all the scope indices in the context.
    pub fn get_scope_indices(&self) -> Range<usize> {
        0..self.scopes.borrow().len()
    }

    /// Iterate over all the decls in the context for the scope with the
    /// given index (fallible).
    pub fn try_for_decls_of_scope_rev<E>(
        &self,
        scope_index: usize,
        mut f: impl FnMut(&ContextMember) -> Result<(), E>,
    ) -> Result<(), E> {
        self.scopes.borrow()[scope_index]
            .decls
            .borrow()
            .iter()
            .rev()
            .try_for_each(|(_, decl)| f(decl))
    }

    /// Iterate over all the decls in the context for the scope with the
    /// given index (fallible).
    pub fn try_for_decls_of_scope<E>(
        &self,
        scope_index: usize,
        mut f: impl FnMut(&ContextMember) -> Result<(), E>,
    ) -> Result<(), E> {
        self.scopes.borrow()[scope_index].decls.borrow().iter().try_for_each(|(_, decl)| f(decl))
    }

    /// Get the number of decls in the context for the scope with the given
    /// index.
    pub fn count_decls_of_scope(&self, scope_index: usize) -> usize {
        self.scopes.borrow()[scope_index].decls.borrow().len()
    }

    /// Iterate over all the decls in the context for the scope with the
    /// given index (reversed).
    pub fn for_all_decls(&self, mut f: impl FnMut(&ContextMember)) {
        for i in self.get_scope_indices() {
            let _ = self.try_for_decls_of_scope(i, |decl| -> Result<(), Infallible> {
                f(decl);
                Ok(())
            });
        }
    }

    /// Iterate over all the decls in the context for the scope with the
    /// given index (reversed).
    pub fn for_all_decls_rev(&self, mut f: impl FnMut(&ContextMember)) {
        for i in self.get_scope_indices().rev() {
            let _ = self.try_for_decls_of_scope_rev(i, |decl| -> Result<(), Infallible> {
                f(decl);
                Ok(())
            });
        }
    }

    /// Iterate over all the decls in the context for the scope with the
    /// given index.
    pub fn for_decls_of_scope(&self, scope_index: usize, mut f: impl FnMut(&ContextMember)) {
        let _ = self.try_for_decls_of_scope(scope_index, |decl| -> Result<(), Infallible> {
            f(decl);
            Ok(())
        });
    }

    /// Iterate over all the decls in the context for the scope with the
    /// given index (reversed).
    pub fn for_decls_of_scope_rev(&self, scope_index: usize, mut f: impl FnMut(&ContextMember)) {
        let _ = self.try_for_decls_of_scope_rev(scope_index, |decl| -> Result<(), Infallible> {
            f(decl);
            Ok(())
        });
    }

    /// Get all the decls in the context for the given scope.
    pub fn get_owned_decls_of_scope(&self, scope_index: usize) -> Vec<SymbolId> {
        self.scopes.borrow()[scope_index].decls.borrow().keys().copied().collect_vec()
    }

    /// Clear all the scopes and decls in the context.
    pub fn clear_all(&self) {
        self.scopes.borrow_mut().clear();
    }

    /// Replace the current context with a new one, for a scoped duration.
    ///
    /// Returns the new scope after running the given function `f`.
    pub fn replace_scoped<T>(&self, new: Context, f: impl FnOnce() -> T) -> (Context, T) {
        let new_scopes = new.scopes;
        let old_context = self.scopes.replace(new_scopes.into_inner());
        let result = f();
        let new_scopes = self.scopes.replace(old_context);
        (Context { scopes: RefCell::new(new_scopes) }, result)
    }

    /// Add a parameter binding
    ///
    /// This should be used when entering a scope that has parameters. Ensure
    /// that the given parameter belongs to the current scope.
    pub fn add_param_binding(&self, param_id: ParamId) {
        let param = param_id.borrow();
        self.add_decl(ContextMember::Typing { name: param.name, ty: param.ty });
    }

    /// Add an assignment without a type.
    pub fn add_typed_assignment(&self, name: SymbolId, ty: TyId, value: TermId) {
        self.add_decl(ContextMember::Typing { name, ty });
        self.add_decl(ContextMember::Assignment { name, value });
    }

    /// Add an assignment without a type.
    pub fn add_assignment(&self, name: SymbolId, term: TermId) {
        debug_assert!(
            self.try_get_decl_ty(name).is_some(),
            "Did not find typing for assignment: {} = {}",
            name,
            term
        );
        self.add_decl(ContextMember::Assignment { name, value: term });
    }

    /// Add a typing binding to the closest stack scope.
    pub fn add_typed_assignment_to_closest_stack(&self, name: SymbolId, ty: TyId, value: TermId) {
        let closest = self.get_closest_stack_scope_ref();
        closest.add_decl(ContextMember::Typing { name, ty });
        closest.add_decl(ContextMember::Assignment { name, value })
    }

    /// Add a typing binding to the closest stack scope.
    pub fn add_typing_to_closest_stack(&self, name: SymbolId, ty: TyId) {
        self.get_closest_stack_scope_ref().add_decl(ContextMember::Typing { name, ty })
    }

    /// Add a typing binding.
    pub fn add_typing(&self, name: SymbolId, ty: TyId) {
        self.add_decl(ContextMember::Typing { name, ty });
    }

    /// Modify the value of an assignment binding.
    pub fn modify_assignment(&self, name: SymbolId, new_value: TermId) {
        self.modify_decl_with(name, |d| match d {
            ContextMember::Typing { name, .. } => {
                panic!("tried to modify typing decl as assignment: {}", name)
            }
            ContextMember::Assignment { name, .. } => {
                ContextMember::Assignment { name, value: new_value }
            }
        })
    }

    /// Add parameter bindings from the given parameters.
    ///
    /// This should be used when entering an already resolved scope that has
    /// parameters.
    pub fn add_param_bindings(&self, params_id: ParamsId) {
        for i in params_id.iter() {
            self.add_param_binding(i);
        }
    }

    /// Add an argument binding to the current scope.
    ///
    /// This should be used when entering a scope that has given arguments, like
    /// a function call, tuple, constructor.
    pub fn add_arg_binding(&self, arg_id: ArgId, param_id: ParamId) {
        let arg = arg_id.borrow();
        let param = param_id.borrow();
        self.add_typed_assignment(param.name, param.ty, arg.value)
    }

    /// Get the value of a binding, if possible.
    pub fn try_get_decl_value(&self, name: SymbolId) -> Option<TermId> {
        self.scopes.borrow().iter().rev().find_map(|scope| match scope.get_decl(name) {
            Some(ContextMember::Assignment { value, .. }) => Some(value),
            _ => None,
        })
    }

    /// Get the type of a binding, if possible.
    pub fn try_get_decl_ty(&self, name: SymbolId) -> Option<TyId> {
        self.scopes.borrow().iter().rev().find_map(|scope| match scope.get_decl(name) {
            Some(ContextMember::Typing { ty, .. }) => Some(ty),
            _ => None,
        })
    }

    /// Get the value of a binding.
    pub fn get_binding_value(&self, name: SymbolId) -> TermId {
        self.try_get_decl_value(name)
            .unwrap_or_else(|| panic!("cannot get value of uninitialised binding {}", name))
    }

    /// Get the type of a binding.
    pub fn get_binding_ty(&self, name: SymbolId) -> TyId {
        self.try_get_decl_ty(name)
            .unwrap_or_else(|| panic!("cannot get type of untyped binding {}", name))
    }

    /// Add argument bindings from the given parameters, using the
    /// given arguments.
    ///
    /// *Invariant*: the lengths of the arguments and parameters must match.
    pub fn add_arg_bindings(&self, params_id: ParamsId, args_id: ArgsId) {
        assert_eq!(params_id.len(), args_id.len());
        for (param, arg) in params_id.iter().zip(args_id.iter()) {
            self.add_arg_binding(arg, param);
        }
    }

    /// Add stack bindings from the given stack, with empty values.
    pub fn add_stack_bindings(&self, stack_id: StackId) {
        let stack = stack_id.borrow();
        for member in &stack.members {
            if let Some(ty) = member.ty {
                self.add_typing(member.name, ty);
                if let Some(value) = member.value {
                    self.add_assignment(member.name, value);
                }
            }
        }
    }

    /// Get the current stack, or panic we are not in a stack.
    pub fn get_current_stack(&self) -> StackId {
        match self.get_current_scope_kind() {
            ScopeKind::Stack(stack_id) => stack_id,
            _ => panic!("get_current_stack called in non-stack scope"),
        }
    }

    /// Get the closest function definition in scope, or `None` if there is
    /// none.
    pub fn get_first_fn_def_in_scope(&self) -> Option<FnDefId> {
        for scope_index in self.get_scope_indices().rev() {
            match self.get_scope(scope_index).kind {
                ScopeKind::Fn(fn_def) => return Some(fn_def),
                _ => continue,
            }
        }
        None
    }

    /// Enter a resolved scope.
    ///
    /// Entering a resolved scope will add all the members of the scope to the
    /// context at once, so that you don't have to add them manually as you
    /// find them.
    pub fn enter_resolved_scope_mut<T, This: HasContext>(
        this: &mut This,
        kind: ScopeKind,
        f: impl FnOnce(&mut This) -> T,
    ) -> T {
        Context::enter_scope_mut(this, kind, |this| {
            this.context().add_resolved_scope_members(kind);
            f(this)
        })
    }

    /// Add the members of the given scope to the context.
    pub fn add_resolved_scope_members(&self, kind: ScopeKind) {
        match kind {
            ScopeKind::Mod(_) => {}
            ScopeKind::Stack(stack_id) => {
                self.add_stack_bindings(stack_id);
            }
            ScopeKind::Fn(fn_def_id) => {
                let fn_def = fn_def_id.borrow();
                self.add_param_bindings(fn_def.ty.params);
            }
            ScopeKind::Data(data_def_id) => {
                let data_def = data_def_id.borrow();

                // Params
                self.add_param_bindings(data_def.params);
            }
            ScopeKind::Ctor(ctor_def_id) => {
                let ctor_def = ctor_def_id.borrow();
                self.add_param_bindings(ctor_def.params);
            }
            ScopeKind::FnTy(fn_ty) => {
                self.add_param_bindings(fn_ty.params);
            }
            ScopeKind::TupleTy(tuple_ty) => {
                self.add_param_bindings(tuple_ty.data);
            }
            ScopeKind::Sub => {
                // No-op
            }
            ScopeKind::Intrinsic(_) => {
                // No-op
            }
        }
    }

    // /// Add the given substitution to the context.
    // pub fn add_sub_to_scope(&self, sub: &Sub) {
    //     for (name, value) in sub.iter() {
    //         self.add_assignment(name, value);
    //     }
    // }

    // /// Enter a scope with the given substitution.
    // pub fn enter_sub_scope<M>(&self, sub: &Sub, f: impl FnOnce() -> M) -> M {
    //     self.enter_scope(ScopeKind::Sub, || {
    //         self.add_sub_to_scope(sub);
    //         f()
    //     })
    // }
}

impl fmt::Display for ContextMember {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ContextMember::Typing { name, ty } => {
                write!(f, "{}: {}", name, ty)
            }
            ContextMember::Assignment { name, value } => {
                write!(f, "{} = {}", name, value)
            }
        }
    }
}

impl fmt::Display for ScopeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScopeKind::Mod(mod_def_id) => write!(f, "mod {}", get!(*mod_def_id, name)),
            ScopeKind::Fn(fn_def_id) => write!(f, "fn {}", get!(*fn_def_id, name)),
            ScopeKind::Data(data_def_id) => write!(f, "data {}", get!(*data_def_id, name)),
            ScopeKind::Ctor(ctor_def) => write!(f, "ctor {}", ctor_def),
            ScopeKind::Stack(stack_def_id) => write!(f, "stack {}", stack_def_id.to_index()),
            ScopeKind::FnTy(fn_ty) => write!(f, "fn ty {}", fn_ty),
            ScopeKind::TupleTy(tuple_ty) => write!(f, "tuple ty {}", tuple_ty),
            ScopeKind::Sub => {
                write!(f, "sub")
            }
            ScopeKind::Intrinsic(intrinsic) => {
                write!(f, "intrinsic {}", intrinsic)
            }
        }
    }
}

impl fmt::Display for Scope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}:", self.kind)?;
        for decl in self.decls.borrow().values() {
            let result = (*decl).to_string();
            for line in result.lines() {
                writeln!(f, "  {line}")?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for scope_index in self.get_scope_indices() {
            let kind = self.get_scope(scope_index).kind;
            writeln!(f, "({}) {}:", scope_index, kind)?;
            self.try_for_decls_of_scope(scope_index, |decl| {
                let result = (*decl).to_string();
                for line in result.lines() {
                    writeln!(f, "  {line}")?;
                }
                Ok(())
            })?;
        }
        Ok(())
    }
}
