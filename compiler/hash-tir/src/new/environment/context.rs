//! Representing and modifying the typechecking context.
use core::fmt;
use std::{
    cell::{Cell, RefCell},
    convert::Infallible,
    ops::Range,
};

use derive_more::From;
use hash_utils::store::{Store, StoreKey};
use indexmap::IndexMap;

use super::env::{AccessToEnv, WithEnv};
use crate::new::{
    data::{CtorDefId, DataDefId},
    fns::{FnDefId, FnTy},
    mods::{ModDefId, ModMemberId},
    params::ParamId,
    scopes::{StackId, StackMemberId},
    symbols::Symbol,
    terms::TermId,
    tuples::TupleTy,
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
    /// A parameter variable
    ///
    /// For example, `(x: i32) => x` or `(T: Type, t: T)`
    Param(ParamId),
    /// Stack member.
    ///
    /// For example, `a` in `{ a := 3; a }`
    StackMember(StackMemberId),
    /// Equality judgement
    ///
    /// This is a special binding because it cannot be referenced by name.
    Equality(EqualityJudgement),
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
}

/// Information about a scope in the context.
#[derive(Debug, Clone, Copy)]
pub struct ScopeInfo {
    /// The kind of the scope.
    pub kind: ScopeKind,
    /// The level of the scope.
    ///
    /// This is an index into the `members` IndexMap in the context, which is
    /// the index of the first member of this scope, if any.
    pub member_level: usize,
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
    members: RefCell<IndexMap<Symbol, BindingKind>>,
    scopes: RefCell<Vec<ScopeInfo>>,
    constant_member_level: Cell<usize>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the current scope level as the "constant" level. Trying to pop this
    /// or above scopes will result in a panic.
    pub fn mark_constant_scope_index(&self) {
        self.constant_member_level.set(self.scopes.borrow().len().saturating_sub(1));
    }

    /// Get the constant scope level.
    pub fn get_constant_scope_index(&self) -> usize {
        self.constant_member_level.get()
    }

    /// Enter a new scope in the context.
    pub fn add_scope(&self, kind: ScopeKind) {
        let member_level = self.members.borrow().len();
        self.scopes.borrow_mut().push(ScopeInfo { kind, member_level });
    }

    /// Exit the last entered scope in the context
    ///
    /// Returns the scope kind that was removed, or `None` if there are no
    /// scopes to remove.
    pub fn remove_scope(&self) -> Option<ScopeInfo> {
        if self.get_current_scope().member_level == self.get_constant_scope_index() {
            panic!("tried to remove a constant scope");
        }
        let removed_scope = self.scopes.borrow_mut().pop()?;
        self.members.borrow_mut().truncate(removed_scope.member_level);
        Some(removed_scope)
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
        self.members.borrow_mut().insert(binding.name, binding.kind);
    }

    /// Get a binding from the context, reading all accessible scopes.
    pub fn get_binding(&self, name: Symbol) -> Option<Binding> {
        Some(Binding { name, kind: self.members.borrow().get(&name).copied()? })
    }

    /// Get information about the current scope.
    pub fn get_current_scope(&self) -> ScopeInfo {
        self.scopes.borrow().last().copied().unwrap_or_else(|| {
            panic!("tried to get the scope kind of a context with no scopes");
        })
    }

    /// Get the index of the current scope.
    pub fn get_current_scope_index(&self) -> usize {
        self.scopes.borrow().len().checked_sub(1).unwrap_or_else(|| {
            panic!("tried to get the scope kind of a context with no scopes");
        })
    }

    /// Get information about the scope with the given index.
    pub fn get_scope(&self, index: usize) -> ScopeInfo {
        self.scopes.borrow()[index]
    }

    /// Get all the scope indices in the context.
    pub fn get_scope_indices(&self) -> Range<usize> {
        0..self.scopes.borrow().len()
    }

    /// Iterate over all the bindings in the context for the scope with the
    /// given index (fallible).
    pub fn try_for_bindings_of_scope<E>(
        &self,
        scope_index: usize,
        mut f: impl FnMut(&Binding) -> Result<(), E>,
    ) -> Result<(), E> {
        let scopes = self.scopes.borrow();
        let current_scope_member_level = scopes[scope_index].member_level;
        let next_scope_member_level = scopes
            .get(scope_index + 1)
            .copied()
            .map(|scope| scope.member_level)
            .unwrap_or(self.members.borrow().len());

        for (&name, &kind) in self
            .members
            .borrow()
            .iter()
            .skip(current_scope_member_level)
            .take(next_scope_member_level - current_scope_member_level)
        {
            f(&Binding { name, kind })?
        }

        Ok(())
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
    pub fn get_owned_bindings_of_scope(&self, level: usize) -> Vec<Symbol> {
        let mut symbols = vec![];
        self.for_bindings_of_scope(level, |binding| symbols.push(binding.name));
        symbols
    }

    /// Clear the scope up to the declared constant scope level.
    pub fn clear_to_constant(&self) {
        let constant_scope_level_index = self.get_constant_scope_index();
        let constant_scope_level = self.get_scope(constant_scope_level_index).member_level;

        self.scopes.borrow_mut().truncate(constant_scope_level_index);
        self.members.borrow_mut().truncate(constant_scope_level);
    }

    /// Clear all the scopes and bindings in the context.
    pub fn clear_all(&self) {
        self.scopes.borrow_mut().clear();
        self.members.borrow_mut().clear();
    }
}

impl fmt::Display for WithEnv<'_, EqualityJudgement> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} === {}", self.env().with(self.value.lhs), self.env().with(self.value.rhs))
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
            BindingKind::Param(param_id) => {
                write!(f, "{}", self.env().with(param_id))
            }
            BindingKind::StackMember(stack_member) => {
                write!(f, "{}", self.env().with(stack_member))
            }
            BindingKind::Equality(equality) => {
                write!(f, "{}", self.env().with(equality))
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
            ScopeKind::Ctor(ctor_def) => write!(f, "ctor {}", self.env().with(ctor_def)),
            ScopeKind::Stack(stack_def_id) => write!(
                f,
                "stack {}",
                self.stores().stack().map_fast(stack_def_id, |stack_def| stack_def.id.to_index())
            ),
            ScopeKind::FnTy(fn_ty) => write!(f, "fn ty {}", self.env().with(&fn_ty)),
            ScopeKind::TupleTy(tuple_ty) => write!(f, "tuple ty {}", self.env().with(&tuple_ty)),
        }
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
