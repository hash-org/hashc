//! Contains context-related utilities.
use derive_more::Constructor;
use hash_utils::store::{SequenceStore, SequenceStoreKey, Store};

use super::common::CommonUtils;
use crate::{
    impl_access_to_env,
    new::{
        args::ArgsId,
        data::{DataDefCtors, DataDefId},
        environment::{
            context::{Binding, BindingKind, EqualityJudgement, ParamOrigin, ScopeKind},
            env::{AccessToEnv, Env},
        },
        mods::ModDefId,
        params::{ParamId, ParamsId},
        scopes::{DeclTerm, StackMemberId},
        terms::TermId,
    },
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
                self.context()
                    .add_binding(Binding { name, kind: BindingKind::StackMember(member_id) })
            }
            _ => panic!("add_stack_binding called in non-stack scope"),
        }
    }

    /// Add the given declaration term to the context.
    ///
    /// This will add all the stack bindings of the declaration to the context
    /// using `add_stack_binding`.
    pub fn add_from_decl_term(&self, decl: &DeclTerm) {
        let current_stack_id = match self.context().get_current_scope().kind {
            ScopeKind::Stack(stack_id) => stack_id,
            _ => unreachable!(), // decls are only allowed in stack scopes
        };

        for stack_index in decl.iter_stack_indices() {
            self.add_stack_binding((current_stack_id, stack_index));
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
}
