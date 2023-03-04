//! Contains context-related utilities.
use derive_more::Constructor;
use hash_utils::store::{CloneStore, SequenceStore, SequenceStoreKey, Store};

use super::{common::CommonUtils, AccessToUtils};
use crate::{
    args::{ArgId, ArgsId},
    data::{DataDefCtors, DataDefId},
    environment::{
        context::{Binding, BindingKind, Context, EqualityJudgement, ParamOrigin, ScopeKind},
        env::{AccessToEnv, Env},
    },
    fns::FnDefId,
    impl_access_to_env,
    mods::ModDefId,
    params::{ParamId, ParamsId},
    pats::Pat,
    scopes::{DeclTerm, StackId, StackIndices, StackMemberId},
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
    pub fn add_param_binding(&self, param_id: ParamId, origin: ParamOrigin) {
        // @@Safety: Maybe we should check that the param belongs to the current scope?
        let name = self.stores().params().map_fast(param_id.0, |params| params[param_id.1].name);
        self.context().add_binding(Binding { name, kind: BindingKind::Param(origin, param_id) });
    }

    /// Add parameter bindings from the given parameters.
    ///
    /// This should be used when entering an already resolved scope that has
    /// parameters.
    pub fn add_param_bindings(&self, params_id: ParamsId, origin: ParamOrigin) {
        self.stores().params().map_fast(params_id, |params| {
            for i in params_id.to_index_range() {
                self.context().add_binding(Binding {
                    name: params[i].name,
                    kind: BindingKind::Param(origin, (params_id, i)),
                });
            }
        });
    }

    /// Add an argument binding to the current scope.
    ///
    /// This should be used when entering a scope that has given arguments, like
    /// a function call, tuple, constructor.
    pub fn add_arg_binding(&self, arg_id: ArgId, param_id: ParamId) {
        self.context().add_binding(Binding {
            name: self.get_param_name(param_id),
            kind: BindingKind::Arg(param_id, arg_id),
        });
    }

    /// Get the given stack binding, or panic if it does not exist.
    pub fn get_stack_binding(&self, name: Symbol) -> (StackMemberId, TyId, Option<TermId>) {
        match self.context().get_binding(name).kind {
            BindingKind::StackMember(member, ty_id, value) => (member, ty_id, value),
            _ => panic!("get_stack_binding called on non-stack binding"),
        }
    }

    /// Get the value of the given stack binding.
    pub fn get_stack_binding_value(&self, name: Symbol) -> Option<TermId> {
        self.get_stack_binding(name).2
    }

    /// Set the value of the given stack binding.
    pub fn set_stack_binding_value(&self, name: Symbol, term_id: TermId) {
        self.context().modify_binding_with(name, |kind| match kind {
            BindingKind::StackMember(member_id, ty, _) => {
                BindingKind::StackMember(member_id, ty, Some(term_id))
            }
            _ => unreachable!("set_stack_binding_value called on non-stack binding"),
        })
    }

    /// Get the type of the given stack binding.
    pub fn get_stack_binding_ty(&self, name: Symbol) -> TyId {
        self.get_stack_binding(name).1
    }

    /// Set the type of the given stack binding.
    pub fn set_stack_binding_ty(&self, name: Symbol, ty: TyId) {
        self.context().modify_binding_with(name, |kind| match kind {
            BindingKind::StackMember(member_id, _, value) => {
                BindingKind::StackMember(member_id, ty, value)
            }
            _ => unreachable!("set_stack_binding_ty called on non-stack binding"),
        })
    }

    /// Get the default type of the given stack member.
    pub fn get_stack_member_ty(&self, member_id: StackMemberId) -> TyId {
        self.stores().stack().map_fast(member_id.0, |stack| stack.members[member_id.1].ty)
    }

    /// Get the type of the given stack member.
    pub fn set_stack_member_ty(&self, member_id: StackMemberId, ty: TyId) {
        self.stores().stack().modify_fast(member_id.0, |stack| stack.members[member_id.1].ty = ty)
    }

    /// Add argument bindings from the given parameters, using the
    /// given arguments.
    ///
    /// *Invariant*: the lengths of the arguments and parameters must match.
    pub fn add_arg_bindings(&self, params_id: ParamsId, args_id: ArgsId) {
        assert_eq!(params_id.len(), args_id.len());
        for i in params_id.to_index_range() {
            self.context().add_binding(Binding {
                name: self.stores().params().map_fast(params_id, |params| params[i].name),
                kind: BindingKind::Arg((params_id, i), (args_id, i)),
            });
        }
    }

    /// Add an equality judgement to the context.
    pub fn add_equality_judgement(&self, lhs: TermId, rhs: TermId) {
        self.context().add_binding(Binding {
            name: self.new_fresh_symbol(),
            kind: BindingKind::Equality(EqualityJudgement { lhs, rhs }),
        });
    }

    /// Add a new stack binding to the current scope context with the default
    /// type for this member.
    ///
    /// *Invariant*: It must be that the member's scope is the current stack
    /// scope.
    pub fn add_stack_binding_with_default_ty(
        &self,
        member_id: StackMemberId,
        value: Option<TermId>,
    ) {
        let ty = self.get_stack_member_ty(member_id);
        self.add_stack_binding(member_id, ty, value);
    }

    /// Add a new stack binding to the current scope context.
    ///
    /// *Invariant*: It must be that the member's scope is the context.
    pub fn add_stack_binding(&self, member_id: StackMemberId, ty: TyId, value: Option<TermId>) {
        let name = self.get_stack_member_name(member_id);
        let stack_scope = self.context().get_closest_stack_scope_ref();
        match stack_scope.kind {
            ScopeKind::Stack(stack_id) => {
                if stack_id != member_id.0 {
                    panic!("add_stack_binding called with member from different stack");
                }
                stack_scope.add_binding(Binding {
                    name,
                    kind: BindingKind::StackMember(member_id, ty, value),
                })
            }
            _ => panic!(
                "add_stack_binding called in non-stack scope: {:?}",
                self.context().get_current_scope_kind()
            ),
        }
    }

    /// Add stack bindings from the given stack, with empty values.
    pub fn add_stack_bindings(&self, stack_id: StackId) {
        self.stores().stack().map_fast(stack_id, |stack| {
            for i in 0..stack.members.len() {
                self.context().add_binding(Binding {
                    name: stack.members[i].name,
                    kind: BindingKind::StackMember((stack_id, i), stack.members[i].ty, None),
                });
            }
        });
    }

    /// Add the given declaration term to the context.
    ///
    /// This will add all the stack bindings of the declaration to the context
    /// using `add_stack_binding`.
    pub fn add_from_decl_term(&self, decl: &DeclTerm) {
        let current_stack_id = match self.context().get_current_scope_kind() {
            ScopeKind::Stack(stack_id) => stack_id,
            _ => unreachable!(), // decls are only allowed in stack scopes
        };

        // @@Todo: fill in complex pats
        if let (Pat::Binding(_), StackIndices::Range { start, end: _ }) =
            (self.get_pat(decl.bind_pat), decl.stack_indices)
        {
            self.stores()
                .stack()
                .modify_fast(current_stack_id, |stack| stack.members[start].ty = decl.ty)
        }

        for stack_index in decl.iter_stack_indices() {
            self.add_stack_binding((current_stack_id, stack_index), decl.ty, decl.value);
        }
    }

    /// Add the data constructors of the given data definition to the context.
    ///
    /// Must be in the scope of the given data definition.
    /// Assumes that the data definition's parameters have already been added.
    pub fn add_data_ctors(&self, data_def_id: DataDefId, f: impl Fn(Binding)) {
        // @@Safety: Maybe we should check that we are in this data def?
        self.stores().data_def().map_fast(data_def_id, |data_def| {
            // Add all the constructors
            match data_def.ctors {
                DataDefCtors::Defined(ctors) => {
                    self.stores().ctor_defs().map_fast(ctors, |ctors| {
                        for ctor in ctors.iter() {
                            let binding = Binding {
                                name: ctor.name,
                                kind: BindingKind::Ctor(data_def_id, ctor.id),
                            };
                            self.context().add_binding(binding);
                            f(binding);
                        }
                    })
                }
                DataDefCtors::Primitive(_) => {
                    // No-op
                }
            }
        })
    }

    /// Add the module's members to the context.
    ///
    /// Must be in the scope of the given module.
    pub fn add_mod_members(&self, mod_def_id: ModDefId, f: impl Fn(Binding)) {
        self.stores().mod_def().map_fast(mod_def_id, |mod_def| {
            self.stores().mod_members().map_fast(mod_def.members, |members| {
                for member in members.iter() {
                    let binding = Binding {
                        name: member.name,
                        kind: BindingKind::ModMember(mod_def_id, member.id),
                    };
                    self.context().add_binding(binding);
                    f(binding);
                }
            })
        })
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
            ScopeKind::Mod(mod_def_id) => {
                self.add_mod_members(mod_def_id, |_| {});
            }
            ScopeKind::Stack(stack_id) => {
                self.add_stack_bindings(stack_id);
            }
            ScopeKind::Fn(fn_def_id) => {
                let fn_def = self.stores().fn_def().get(fn_def_id);
                self.add_param_bindings(fn_def.ty.params, ParamOrigin::Fn(fn_def_id));
            }
            ScopeKind::Data(data_def_id) => {
                let data_def = self.stores().data_def().get(data_def_id);

                // Params
                self.add_param_bindings(data_def.params, ParamOrigin::Data(data_def_id));

                // Constructors
                self.add_data_ctors(data_def_id, |_| {});
            }
            ScopeKind::Ctor(ctor_def_id) => {
                let ctor_def = self.stores().ctor_defs().get_element(ctor_def_id);
                self.add_param_bindings(ctor_def.params, ParamOrigin::Ctor(ctor_def_id));
            }
            ScopeKind::FnTy(fn_ty) => {
                self.add_param_bindings(fn_ty.params, ParamOrigin::FnTy(fn_ty));
            }
            ScopeKind::TupleTy(tuple_ty) => {
                self.add_param_bindings(tuple_ty.data, ParamOrigin::TupleTy(tuple_ty));
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
}
