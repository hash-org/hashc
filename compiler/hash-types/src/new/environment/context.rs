//! Representing and modifying the typechecking context.
use core::fmt;
use std::{cell::RefCell, convert::Infallible};

use derive_more::From;
use hash_utils::store::{Store, StoreKey};
use indexmap::IndexMap;

use super::env::{AccessToEnv, WithEnv};
use crate::new::{
    data::{CtorDefId, DataDefId},
    fns::FnDefId,
    mods::{ModDefId, ModMemberId},
    params::{DefParamIndex, ParamIndex},
    scopes::{StackId, StackMemberId},
    symbols::Symbol,
    tys::TyId,
    utils::common::CommonUtils,
};
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
    /// A binding that represents a parameter variable of a function.
    ///
    /// For example, `(x: i32) => x`
    BoundVar(BoundVarOrigin),
}

/// All the different places a bound variable can originate from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundVarOrigin {
    /// Module parameter.
    ///
    /// For example, `T` in `mod <T> { x: (t: T) -> void }`
    Mod(ModDefId, DefParamIndex),
    /// Function parameter.
    ///
    /// For example, `x` in `(x: i32) => x`
    Fn(FnDefId, ParamIndex),
    /// Function type.
    ///
    /// Invariant: the inner type is `FnTy`.
    ///
    /// For example, `x` in `type (x: i32) -> Foo<x>`
    FnTy(TyId, ParamIndex),
    /// Data definition parameter.
    ///
    /// For example, `T` in `Foo := struct <T> (x: T)`
    Data(DataDefId, DefParamIndex),
    /// Stack member.
    ///
    /// For example, `a` in `{ a := 3; a }`
    StackMember(StackMemberId),
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

/// All the different kinds of scope there are, and their associated data.
#[derive(Debug, Clone, Copy, PartialEq, Eq, From)]
pub enum ScopeKind {
    /// A module scope.
    Mod(ModDefId),
    // A stack scope.
    Stack(StackId),
    /// A function scope.
    Fn(FnDefId),
    /// A data definition.
    Data(DataDefId),
    /// A function type scope.
    ///
    /// The inner type points to an `FnTy` variant.
    FnTy(TyId),
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
    scope_levels: RefCell<Vec<usize>>,
    members: RefCell<IndexMap<Symbol, Binding>>,
    scope_kinds: RefCell<Vec<ScopeKind>>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    /// Enter a new scope in the context.
    pub fn add_scope(&self, kind: ScopeKind) {
        self.scope_kinds.borrow_mut().push(kind);
        self.scope_levels.borrow_mut().push(self.members.borrow().len());
    }

    /// Exit the last entered scope in the context
    ///
    /// Returns the scope kind that was removed, or `None` if there are no
    /// scopes to remove.
    pub fn remove_scope(&self) -> Option<ScopeKind> {
        match (self.scope_levels.borrow_mut().pop(), self.scope_kinds.borrow_mut().pop()) {
            (Some(last_level), Some(last_kind)) => {
                self.members.borrow_mut().truncate(last_level);
                Some(last_kind)
            }
            (None, None) => None,
            _ => panic!("mismatch in lengths of `scope_levels` and `kinds`"),
        }
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
    pub fn add_binding(&self, binding: Binding) {
        self.members.borrow_mut().insert(binding.name, binding);
    }

    /// Get a binding from the context, reading all accessible scopes.
    pub fn get_binding(&self, name: Symbol) -> Option<Binding> {
        self.members.borrow().get(&name).copied()
    }

    /// Get the kind of the current scope.
    pub fn get_current_scope_kind(&self) -> ScopeKind {
        self.scope_kinds.borrow().last().copied().unwrap_or_else(|| {
            panic!("tried to get the scope kind of a context with no scopes");
        })
    }

    /// Get the current scope level.
    pub fn get_current_scope_level(&self) -> usize {
        let scope_levels = self.scope_levels.borrow();
        if scope_levels.is_empty() {
            panic!("tried to get the scope level of a context with no scopes");
        }
        scope_levels.len() - 1
    }

    /// Get all the scope levels in the context.
    pub fn get_scope_levels(&self) -> impl Iterator<Item = usize> {
        0..self.scope_levels.borrow().len()
    }

    /// Get the scope kind of the given scope level.
    pub fn get_scope_kind_of_level(&self, level: usize) -> ScopeKind {
        self.scope_kinds.borrow()[level]
    }

    /// Iterate over all the bindings in the context for the given scope level
    /// (fallible).
    pub fn try_for_bindings_of_level<E>(
        &self,
        level: usize,
        mut f: impl FnMut(&Binding) -> Result<(), E>,
    ) -> Result<(), E> {
        let scope_levels = self.scope_levels.borrow();
        let current_level_member_index = scope_levels[level];
        let next_level_member_index =
            scope_levels.get(level + 1).copied().unwrap_or(self.members.borrow().len());
        for (_, binding) in self
            .members
            .borrow()
            .iter()
            .skip(current_level_member_index)
            .take(next_level_member_index - current_level_member_index)
        {
            f(binding)?
        }
        Ok(())
    }

    /// Iterate all the bindings in the context for the given scope level.
    pub fn for_bindings_of_level(&self, level: usize, mut f: impl FnMut(&Binding)) {
        let _ = self.try_for_bindings_of_level(level, |binding| -> Result<(), Infallible> {
            f(binding);
            Ok(())
        });
    }

    /// Get all the bindings in the context for the given scope level.
    pub fn get_bindings_of_level(&self, level: usize) -> Vec<Symbol> {
        let mut symbols = vec![];
        self.for_bindings_of_level(level, |binding| symbols.push(binding.name));
        symbols
    }
}

impl fmt::Display for WithEnv<'_, &BoundVarOrigin> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            BoundVarOrigin::Mod(mod_def_id, param_index) => {
                let def_params_id =
                    self.stores().mod_def().map_fast(*mod_def_id, |mod_def| mod_def.params);
                let param = self.get_def_param_by_index(def_params_id, *param_index);
                write!(f, "{}", self.env().with(&param))
            }
            BoundVarOrigin::Data(data_def_id, param_index) => {
                let def_params_id =
                    self.stores().data_def().map_fast(*data_def_id, |mod_def| mod_def.params);
                let param = self.get_def_param_by_index(def_params_id, *param_index);
                write!(f, "{}", self.env().with(&param))
            }
            BoundVarOrigin::FnTy(_fn_ty_id, _param_index) => {
                todo!()
            }
            BoundVarOrigin::Fn(_, _param_id) => todo!(),
            BoundVarOrigin::StackMember(stack_member) => {
                write!(f, "{}", self.env().with(*stack_member))
            }
        }
    }
}

impl fmt::Display for WithEnv<'_, Binding> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value.kind {
            BindingKind::ModMember(_, member_id) => {
                write!(f, "{}", self.env().with(member_id))
            }
            BindingKind::Ctor(_, ctor_id) => {
                write!(f, "{}", self.env().with(ctor_id))
            }
            BindingKind::BoundVar(bound_var) => {
                write!(f, "{}", self.env().with(&bound_var))
            }
        }
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
            ScopeKind::Stack(stack_def_id) => write!(
                f,
                "stack {}",
                self.stores().stack().map_fast(stack_def_id, |stack_def| stack_def.id.to_index())
            ),
            ScopeKind::FnTy(fn_ty) => self
                .stores()
                .ty()
                .map_fast(fn_ty, |fn_ty| write!(f, "fn ty {}", self.env().with(fn_ty),)),
        }
    }
}

impl fmt::Display for WithEnv<'_, &Context> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for scope_level in self.value.get_scope_levels() {
            let kind = self.value.get_scope_kind_of_level(scope_level);
            writeln!(f, "({}) {}:", scope_level, self.env().with(kind))?;
            self.value.try_for_bindings_of_level(scope_level, |binding| {
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
