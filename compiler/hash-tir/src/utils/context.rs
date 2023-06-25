//! Contains context-related utilities.

use derive_more::Constructor;
use hash_utils::store::{CloneStore, SequenceStore, SequenceStoreKey, Store};

use super::{common::CommonUtils, AccessToUtils};
use crate::{
    args::{ArgId, ArgsId},
    context::{Context, Decl, ScopeKind},
    environment::env::{AccessToEnv, Env},
    fns::FnDefId,
    impl_access_to_env,
    params::{ParamId, ParamsId},
    scopes::StackId,
    sub::Sub,
    symbols::Symbol,
    terms::TermId,
    tys::TyId,
};

/// Context-related utilities.
#[derive(Constructor)]
pub struct ContextUtils<'env> {
    env: &'env Env<'env>,
}

impl_access_to_env!(ContextUtils<'tc>);

impl<'env> ContextUtils<'env> {
    /// Add a parameter binding
    ///
    /// This should be used when entering a scope that has parameters. Ensure
    /// that the given parameter belongs to the current scope.
    pub fn add_param_binding(&self, param_id: ParamId) {
        let param = self.get_param(param_id);
        self.context().add_decl(param.name, Some(param.ty), None);
    }

    /// Add an assignment without a type.
    pub fn add_unknown_var(&self, name: Symbol) {
        self.context().add_decl(name, None, None);
    }

    /// Add an assignment without a type.
    pub fn add_untyped_assignment(&self, name: Symbol, term: TermId) {
        self.context().add_decl(name, None, Some(term));
    }

    /// Add a typing binding to the closest stack scope.
    pub fn add_assignment_to_closest_stack(&self, name: Symbol, ty: TyId, value: TermId) {
        self.context().get_closest_stack_scope_ref().add_decl(Decl {
            name,
            ty: Some(ty),
            value: Some(value),
        })
    }

    /// Add a typing binding to the closest stack scope.
    pub fn add_typing_to_closest_stack(&self, name: Symbol, ty: TyId) {
        self.context().get_closest_stack_scope_ref().add_decl(Decl {
            name,
            ty: Some(ty),
            value: None,
        })
    }

    /// Add a typing binding.
    pub fn add_typing(&self, name: Symbol, ty: TyId) {
        self.context().add_decl(name, Some(ty), None);
    }

    /// Add an assignment binding with a value.
    pub fn add_assignment(&self, name: Symbol, ty: TyId, value: TermId) {
        self.context().add_decl(name, Some(ty), Some(value));
    }

    /// Modify the type of an assignment binding.
    pub fn modify_typing(&self, name: Symbol, new_ty: TyId) {
        let current_value = self.try_get_decl_value(name);
        self.context().modify_decl(Decl { name, ty: Some(new_ty), value: current_value })
    }

    /// Modify the value of an assignment binding.
    pub fn modify_assignment(&self, name: Symbol, new_value: TermId) {
        let current_ty = self.try_get_decl_ty(name);
        self.context().modify_decl(Decl { name, ty: current_ty, value: Some(new_value) })
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
        let arg = self.get_arg(arg_id);
        let param = self.get_param(param_id);
        self.context().add_decl(param.name, Some(param.ty), Some(arg.value));
    }

    /// Get a binding from the current scopes.
    pub fn get_decl(&self, name: Symbol) -> Decl {
        self.context()
            .try_get_decl(name)
            .unwrap_or_else(|| panic!("cannot get binding for {}", self.env().with(name),))
    }

    /// Get the value of a binding, if possible.
    pub fn try_get_decl_value(&self, name: Symbol) -> Option<TermId> {
        self.context().try_get_decl(name)?.value
    }

    /// Get the type of a binding, if possible.
    pub fn try_get_decl_ty(&self, name: Symbol) -> Option<TyId> {
        self.context().try_get_decl(name)?.ty
    }

    /// Get the value of a binding.
    pub fn get_binding_value(&self, name: Symbol) -> TermId {
        self.try_get_decl_value(name).unwrap_or_else(|| {
            panic!("cannot get value of uninitialised binding {}", self.env().with(name))
        })
    }

    /// Get the type of a binding.
    pub fn get_binding_ty(&self, name: Symbol) -> TyId {
        self.try_get_decl_ty(name).unwrap_or_else(|| {
            panic!("cannot get type of untyped binding {}", self.env().with(name))
        })
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
        self.stores().stack().map_fast(stack_id, |stack| {
            for member in &stack.members {
                self.context().add_decl(member.name, member.ty, member.value);
            }
        });
    }

    /// Get the current stack, or panic we are not in a stack.
    pub fn get_current_stack(&self) -> StackId {
        match self.context().get_current_scope_kind() {
            ScopeKind::Stack(stack_id) => stack_id,
            _ => panic!("get_current_stack called in non-stack scope"),
        }
    }

    /// Get the closest function definition in scope, or `None` if there is
    /// none.
    pub fn get_first_fn_def_in_scope(&self) -> Option<FnDefId> {
        for scope_index in self.context().get_scope_indices().rev() {
            match self.context().get_scope(scope_index).kind {
                ScopeKind::Fn(fn_def) => return Some(fn_def),
                _ => continue,
            }
        }
        None
    }

    /// Add the members of the given scope to the context.
    pub fn add_resolved_scope_members(&self, kind: ScopeKind) {
        match kind {
            ScopeKind::Mod(_) => {}
            ScopeKind::Stack(stack_id) => {
                self.add_stack_bindings(stack_id);
            }
            ScopeKind::Fn(fn_def_id) => {
                let fn_def = self.stores().fn_def().get(fn_def_id);
                self.add_param_bindings(fn_def.ty.params);
            }
            ScopeKind::Data(data_def_id) => {
                let data_def = self.stores().data_def().get(data_def_id);

                // Params
                self.add_param_bindings(data_def.params);
            }
            ScopeKind::Ctor(ctor_def_id) => {
                let ctor_def = self.stores().ctor_defs().get_element(ctor_def_id);
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
        }
    }

    /// Enter a resolved scope.
    ///
    /// Entering a resolved scope will add all the members of the scope to the
    /// context at once, so that you don't have to add them manually as you
    /// find them.
    pub fn enter_resolved_scope_mut<T, This: AccessToEnv>(
        this: &mut This,
        kind: ScopeKind,
        f: impl FnOnce(&mut This) -> T,
    ) -> T {
        Context::enter_scope_mut(this, kind, |this| {
            this.context_utils().add_resolved_scope_members(kind);
            f(this)
        })
    }

    /// Add the given substitution to the context.
    pub fn add_sub_to_scope(&self, sub: &Sub) {
        for (name, value) in sub.iter() {
            match self.try_get_decl_ty(name) {
                Some(ty) => {
                    self.add_assignment(name, ty, value);
                }
                None => {
                    self.add_untyped_assignment(name, value);
                }
            }
        }
    }

    /// Enter a scope with the given substitution.
    pub fn enter_sub_scope<M>(&self, sub: &Sub, f: impl FnOnce() -> M) -> M {
        self.context().enter_scope(ScopeKind::Sub, || {
            self.add_sub_to_scope(sub);
            f()
        })
    }
}
