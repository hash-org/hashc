//! Contains context-related operations, building on top of `Context` defined in
//! `hash-tir`.
// @@Todo: move this to hash-tir?
use derive_more::Constructor;
use hash_tir::{
    new::{
        data::DataDefCtors,
        defs::DefParamsId,
        environment::{
            context::{Binding, BindingKind, BoundVarOrigin, ScopeKind},
            env::AccessToEnv,
        },
        params::{DefParamIndex, ParamId, ParamsId},
        scopes::StackMemberId,
    },
    ty_as_variant,
};
use hash_utils::store::{SequenceStore, Store};

use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

/// Context-related operations.
#[derive(Constructor)]
pub struct ContextOps<'env> {
    tc_env: &'env TcEnv<'env>,
}

impl_access_to_tc_env!(ContextOps<'tc>);

impl<'env> ContextOps<'env> {
    /// Enter a new scope, and add all the appropriate bindings to it depending
    /// on the scope kind.
    ///
    /// This will add all the scope bindings to the context for the duration of
    /// the closure, unless the scope is a stack scope, in which case the
    /// bindings should be added to the context using
    /// [`ContextOps::add_stack_binding()`].
    pub fn enter_scope<T>(&self, kind: ScopeKind, f: impl FnOnce() -> T) -> T {
        let result = self.context().enter_scope(kind, || {
            self.add_bindings_from_scope_kind(kind);
            f()
        });
        result
    }

    /// Add the given scope to the context.
    ///
    /// This will add all the scope bindings to the context, and the scope
    /// should be manually exited using [`Context::remove_scope()`] if
    /// necessary.
    ///
    /// Prefer `enter_scope` if possible.
    pub fn add_scope(&self, kind: ScopeKind) {
        self.context().add_scope(kind);
        self.add_bindings_from_scope_kind(kind);
    }

    /// Add a new stack binding to the current scope context.
    ///
    /// *Invariant*: It must be that the member's scope is the current stack
    /// scope.
    pub fn add_stack_binding(&self, member_id: StackMemberId) {
        match self.context().get_current_scope().kind {
            ScopeKind::Stack(stack_id) => {
                if stack_id != member_id.0 {
                    panic!("add_stack_binding called with member from different stack");
                }
                let name = self
                    .stores()
                    .stack()
                    .map_fast(stack_id, |stack| stack.members[member_id.1].name);
                self.context().add_binding(Binding {
                    name,
                    kind: BindingKind::BoundVar(BoundVarOrigin::StackMember(member_id)),
                })
            }
            _ => panic!("add_stack_binding called in non-stack scope"),
        }
    }

    /// Add the given set of parameters to the context as bound variables.
    ///
    /// The `bound_var_origin_from_param` function is used to determine the
    /// origin of the bound variable, based on the parameter.
    fn add_params_to_context(
        &self,
        params_id: ParamsId,
        bound_var_origin_from_param: impl Fn(ParamId) -> BoundVarOrigin,
    ) {
        self.stores().params().map_fast(params_id, |params| {
            for param in params.iter() {
                self.context().add_binding(Binding {
                    name: param.name,
                    kind: BindingKind::BoundVar(bound_var_origin_from_param(param.id)),
                });
            }
        })
    }

    /// Add the given set of definition parameters to the context as bound
    /// variables.
    ///
    /// The `bound_var_origin_from_param` function is used to determine the
    /// origin of the bound variable, based on the parameter group and
    /// parameter.
    fn add_def_params_to_context(
        &self,
        def_params_id: DefParamsId,
        bound_var_origin_from_param: impl Fn(DefParamIndex) -> BoundVarOrigin,
    ) {
        self.stores().def_params().map_fast(def_params_id, |def_params| {
            for (i, def_param_group) in def_params.iter().enumerate() {
                self.add_params_to_context(def_param_group.params, |param| {
                    bound_var_origin_from_param(DefParamIndex {
                        group_index: i,
                        param_index: param.1.into(),
                    })
                })
            }
        })
    }

    /// Add all the scope bindings corresponding to the given scope kind to the
    /// context, unless the scope is a stack scope.
    fn add_bindings_from_scope_kind(&self, kind: ScopeKind) {
        match kind {
            ScopeKind::Stack(_) => {
                // Here we don't add anything because the stack bindings are
                // added manually.
            }
            ScopeKind::Mod(mod_def_id) => {
                self.stores().mod_def().map_fast(mod_def_id, |mod_def| {
                    // Add all the module bindings
                    self.stores().mod_members().map_fast(mod_def.members, |members| {
                        for member in members.iter() {
                            self.context().add_binding(Binding {
                                name: member.name,
                                kind: BindingKind::ModMember(mod_def_id, member.id),
                            });
                        }
                    })
                })
            }
            ScopeKind::Fn(fn_def_id) => {
                self.stores().fn_def().map_fast(fn_def_id, |fn_def| {
                    // Add all the parameters
                    self.add_params_to_context(fn_def.ty.params, |param_id| {
                        BoundVarOrigin::Fn(fn_def_id, param_id.into())
                    })
                })
            }
            ScopeKind::Data(data_def_id) => {
                self.stores().data_def().map_fast(data_def_id, |data_def| {
                    // Add all the parameters
                    self.add_def_params_to_context(data_def.params, |def_param_index| {
                        BoundVarOrigin::Data(data_def_id, def_param_index)
                    });

                    // Add all the constructors
                    match data_def.ctors {
                        DataDefCtors::Defined(ctors) => {
                            self.stores().ctor_defs().map_fast(ctors, |ctors| {
                                for ctor in ctors.iter() {
                                    self.context().add_binding(Binding {
                                        name: ctor.name,
                                        kind: BindingKind::Ctor(data_def_id, ctor.id),
                                    });
                                }
                            })
                        }
                        DataDefCtors::Primitive(_) => {
                            // No-op
                        }
                    }
                })
            }
            ScopeKind::FnTy(fn_ty_id) => {
                // Add all the parameters
                let fn_ty = self
                    .stores()
                    .ty()
                    .map_fast(fn_ty_id, |fn_ty_val| ty_as_variant!(self, value {*fn_ty_val}, Fn));
                self.add_params_to_context(fn_ty.params, |param_id| {
                    BoundVarOrigin::FnTy(fn_ty_id, param_id.into())
                })
            }
        }
    }
}