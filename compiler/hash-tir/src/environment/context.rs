//! Representing and modifying the typechecking context.
use core::fmt;
use std::{
    cell::{Ref, RefCell},
    convert::Infallible,
    ops::Range,
};

use derive_more::From;
use hash_utils::{
    itertools::Itertools,
    store::{Store, StoreKey},
};
use indexmap::IndexMap;

use super::env::{AccessToEnv, WithEnv};
use crate::{
    data::{CtorDefId, DataDefId},
    fns::{FnDefId, FnTy},
    mods::{ModDefId, ModMemberId},
    scopes::StackId,
    symbols::Symbol,
    terms::TermId,
    tuples::TupleTy,
    tys::TyId,
};

/// All the places a parameter can come from.
#[derive(Debug, Clone, Copy, From)]
pub enum ParamOrigin {
    /// A parameter in a function definition.
    Fn(FnDefId),
    /// A parameter in a function type.
    FnTy(FnTy),
    /// A parameter in a tuple type.
    TupleTy(TupleTy),
    /// A parameter in a constructor.
    Ctor(CtorDefId),
    /// A parameter in a data definition.
    Data(DataDefId),
}

impl From<ParamOrigin> for ScopeKind {
    fn from(value: ParamOrigin) -> Self {
        match value {
            ParamOrigin::Fn(fn_def_id) => ScopeKind::Fn(fn_def_id),
            ParamOrigin::FnTy(fn_ty) => ScopeKind::FnTy(fn_ty),
            ParamOrigin::TupleTy(tuple_ty) => ScopeKind::TupleTy(tuple_ty),
            ParamOrigin::Ctor(ctor_def_id) => ScopeKind::Ctor(ctor_def_id),
            ParamOrigin::Data(data_def_id) => ScopeKind::Data(data_def_id),
        }
    }
}

impl ParamOrigin {
    /// A constant parameter is one that cannot depend on non-constant bindings.
    pub fn is_constant(&self) -> bool {
        match self {
            ParamOrigin::Fn(_) | ParamOrigin::FnTy(_) | ParamOrigin::TupleTy(_) => false,
            ParamOrigin::Ctor(_) | ParamOrigin::Data(_) => true,
        }
    }
}

/// A binding that contains a type and optional value.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Decl {
    pub name: Symbol,
    pub ty: Option<TyId>,
    pub value: Option<TermId>,
}

/// The kind of a binding.
#[derive(Debug, Clone, Copy)]
pub enum BindingKind {
    /// A binding that is a module member.
    ///
    /// For example, `mod { Q := struct(); Q }`
    ModMember(ModDefId, ModMemberId),
    /// A binding that is a constructor definition.
    ///
    /// For example, `false`, `None`, `Some(_)`.
    Ctor(DataDefId, CtorDefId),
    /// A binding that contains a type and optional value.
    Decl(Decl),
}

impl BindingKind {
    /// A constant binding is one that cannot depend on non-constant bindings.
    pub fn is_constant(&self) -> bool {
        match self {
            BindingKind::ModMember(_, _) | BindingKind::Ctor(_, _) => true,
            BindingKind::Decl(_) => false,
        }
    }
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

/// An established equality between terms, that is in scope.
#[derive(Debug, Clone, Copy)]
pub struct EqualityJudgement {
    pub lhs: TermId,
    pub rhs: TermId,
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

impl ScopeKind {
    /// Whether this scope is constant.
    ///
    /// A constant scope is one that cannot depend on non-constant bindings.
    pub fn is_constant(&self) -> bool {
        match self {
            ScopeKind::Mod(_) | ScopeKind::Data(_) | ScopeKind::Ctor(_) => true,
            ScopeKind::Sub
            | ScopeKind::Stack(_)
            | ScopeKind::Fn(_)
            | ScopeKind::FnTy(_)
            | ScopeKind::TupleTy(_) => false,
        }
    }
}

/// Information about a scope in the context.
#[derive(Debug, Clone)]
pub struct Scope {
    /// The kind of the scope.
    pub kind: ScopeKind,
    /// The bindings of the scope
    pub bindings: RefCell<IndexMap<Symbol, BindingKind>>,
}

impl Scope {
    /// Create a new scope with the given kind.
    pub fn with_empty_members(kind: ScopeKind) -> Self {
        Self { kind, bindings: RefCell::new(IndexMap::new()) }
    }

    /// Add a binding to the scope.
    pub fn add_binding(&self, binding: Binding) {
        self.bindings.borrow_mut().insert(binding.name, binding.kind);
    }

    /// Get the binding corresponding to the given symbol.
    pub fn get_binding(&self, symbol: Symbol) -> Option<Binding> {
        self.bindings.borrow().get(&symbol).map(|kind| Binding { name: symbol, kind: *kind })
    }

    /// Set an existing binding kind of the given symbol.
    ///
    /// Returns `true` if the binding was found and updated, `false` otherwise.
    pub fn set_existing_binding_kind(
        &self,
        symbol: Symbol,
        kind: &impl Fn(BindingKind) -> BindingKind,
    ) -> bool {
        if let Some(old) = self.get_binding_kind(symbol) {
            self.bindings.borrow_mut().insert(symbol, kind(old));
            true
        } else {
            false
        }
    }

    /// Get a binding reference corresponding to the given symbol.
    pub fn get_binding_kind(&self, symbol: Symbol) -> Option<BindingKind> {
        let bindings = self.bindings.borrow();
        bindings.get(&symbol).copied()
    }
}

/// Data structure managing the typechecking context.
///
/// The context is a stack of scopes, each scope being a stack in itself.
///
/// The context is used to resolve symbols to their corresponding bindings, and
/// thus interpret their meaning. It can read and add [`Binding`]s, and can
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
    pub fn enter_scope_mut<T, This: AccessToEnv>(
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

    /// Add a new binding to the current scope context.
    pub fn add_decl(&self, name: Symbol, ty: Option<TyId>, value: Option<TermId>) {
        self.get_current_scope_ref()
            .add_binding(Binding { name, kind: BindingKind::Decl(Decl { name, ty, value }) })
    }

    /// Add a new binding to the current scope context.
    pub fn add_binding(&self, binding: Binding) {
        self.get_current_scope_ref().add_binding(binding)
    }

    /// Add a new binding to the scope with the given index.
    pub fn add_binding_to_scope(&self, binding: Binding, _scope_index: usize) {
        self.get_closest_stack_scope_ref().add_binding(binding);
    }

    /// Get a binding from the context, reading all accessible scopes.
    pub fn try_get_binding(&self, name: Symbol) -> Option<Binding> {
        self.scopes.borrow().iter().rev().find_map(|scope| scope.get_binding(name))
    }

    /// Get a binding from the context, reading all accessible scopes.
    ///
    /// Panics if the binding doesn't exist.
    pub fn get_binding(&self, name: Symbol) -> Binding {
        self.try_get_binding(name)
            .unwrap_or_else(|| panic!("tried to get a binding that doesn't exist"))
    }

    /// Modify a binding in the context, with a function that takes the current
    /// binding kind and returns the new binding kind.
    pub fn modify_binding_with(&self, name: Symbol, binding: impl Fn(BindingKind) -> BindingKind) {
        let _ = self
            .scopes
            .borrow()
            .iter()
            .rev()
            .find(|scope| scope.set_existing_binding_kind(name, &binding))
            .unwrap_or_else(|| panic!("tried to modify a binding that doesn't exist"));
    }

    /// Modify a binding in the context.
    pub fn modify_binding(&self, binding: Binding) {
        self.modify_binding_with(binding.name, |_| binding.kind);
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

    /// Iterate over all the bindings in the context for the scope with the
    /// given index (fallible).
    pub fn try_for_bindings_of_scope_rev<E>(
        &self,
        scope_index: usize,
        mut f: impl FnMut(&Binding) -> Result<(), E>,
    ) -> Result<(), E> {
        self.scopes.borrow()[scope_index]
            .bindings
            .borrow()
            .iter()
            .rev()
            .try_for_each(|binding| f(&Binding { name: *binding.0, kind: *binding.1 }))
    }

    /// Iterate over all the bindings in the context for the scope with the
    /// given index (fallible).
    pub fn try_for_bindings_of_scope<E>(
        &self,
        scope_index: usize,
        mut f: impl FnMut(&Binding) -> Result<(), E>,
    ) -> Result<(), E> {
        self.scopes.borrow()[scope_index]
            .bindings
            .borrow()
            .iter()
            .try_for_each(|binding| f(&Binding { name: *binding.0, kind: *binding.1 }))
    }

    /// Get the number of bindings in the context for the scope with the given
    /// index.
    pub fn count_bindings_of_scope(&self, scope_index: usize) -> usize {
        self.scopes.borrow()[scope_index].bindings.borrow().len()
    }

    /// Iterate over all the bindings in the context for the scope with the
    /// given index (reversed).
    pub fn for_bindings_of_scope_rev(&self, scope_index: usize, mut f: impl FnMut(&Binding)) {
        let _ =
            self.try_for_bindings_of_scope_rev(scope_index, |binding| -> Result<(), Infallible> {
                f(binding);
                Ok(())
            });
    }

    /// Iterate over all the bindings in the context for the scope with the
    /// given index.
    pub fn for_bindings_of_scope(&self, scope_index: usize, mut f: impl FnMut(&Binding)) {
        let _ = self.try_for_bindings_of_scope(scope_index, |binding| -> Result<(), Infallible> {
            f(binding);
            Ok(())
        });
    }

    /// Get all the bindings in the context for the given scope.
    pub fn get_owned_bindings_of_scope(&self, scope_index: usize) -> Vec<Symbol> {
        self.scopes.borrow()[scope_index].bindings.borrow().keys().copied().collect_vec()
    }

    /// Clear all the scopes and bindings in the context.
    pub fn clear_all(&self) {
        self.scopes.borrow_mut().clear();
    }
}

impl fmt::Display for WithEnv<'_, EqualityJudgement> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} === {}", self.env().with(self.value.lhs), self.env().with(self.value.rhs))
    }
}

impl fmt::Display for WithEnv<'_, Decl> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ty_or_unknown = {
            if let Some(ty) = self.value.ty {
                self.env().with(ty).to_string()
            } else {
                "unknown".to_string()
            }
        };
        match self.value.value {
            Some(value) => {
                write!(
                    f,
                    "{}: {} = {}",
                    self.env().with(self.value.name),
                    ty_or_unknown,
                    self.env().with(value)
                )
            }
            None => {
                write!(f, "{}: {}", self.env().with(self.value.name), ty_or_unknown)
            }
        }
    }
}

impl fmt::Display for WithEnv<'_, BindingKind> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            BindingKind::ModMember(_, member_id) => {
                write!(f, "{}", self.env().with(member_id))
            }
            BindingKind::Ctor(_, ctor_id) => {
                write!(f, "{}", self.env().with(ctor_id))
            }
            BindingKind::Decl(decl) => {
                write!(f, "{}", self.env().with(decl))
            }
        }
    }
}

impl fmt::Display for WithEnv<'_, Binding> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.env().with(self.value.kind))
    }
}

impl fmt::Display for WithEnv<'_, ScopeKind> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            ScopeKind::Mod(mod_def_id) => write!(
                f,
                "mod {}",
                self.stores()
                    .mod_def()
                    .map_fast(mod_def_id, |mod_def| self.env().with(mod_def.name))
            ),
            ScopeKind::Fn(fn_def_id) => write!(
                f,
                "fn {}",
                self.stores().fn_def().map_fast(fn_def_id, |fn_def| self.env().with(fn_def.name))
            ),
            ScopeKind::Data(data_def_id) => write!(
                f,
                "data {}",
                self.stores()
                    .data_def()
                    .map_fast(data_def_id, |data_def| self.env().with(data_def.name))
            ),
            ScopeKind::Ctor(ctor_def) => write!(f, "ctor {}", self.env().with(ctor_def)),
            ScopeKind::Stack(stack_def_id) => write!(
                f,
                "stack {}",
                self.stores().stack().map_fast(stack_def_id, |stack_def| stack_def.id.to_index())
            ),
            ScopeKind::FnTy(fn_ty) => write!(f, "fn ty {}", self.env().with(&fn_ty)),
            ScopeKind::TupleTy(tuple_ty) => write!(f, "tuple ty {}", self.env().with(&tuple_ty)),
            ScopeKind::Sub => {
                write!(f, "sub")
            }
        }
    }
}

impl fmt::Display for WithEnv<'_, &Scope> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}:", self.env().with(self.value.kind))?;
        for binding in self.value.bindings.borrow().values() {
            let result = self.env().with(*binding).to_string();
            for line in result.lines() {
                writeln!(f, "  {line}")?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for WithEnv<'_, &Context> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for scope_index in self.value.get_scope_indices() {
            let kind = self.value.get_scope(scope_index).kind;
            writeln!(f, "({}) {}:", scope_index, self.env().with(kind))?;
            self.value.try_for_bindings_of_scope(scope_index, |binding| {
                let result = self.env().with(*binding).to_string();
                for line in result.lines() {
                    writeln!(f, "  {line}")?;
                }
                Ok(())
            })?;
        }
        Ok(())
    }
}
