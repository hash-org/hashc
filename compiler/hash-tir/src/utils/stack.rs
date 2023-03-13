//! Utilities for managing stacks and their members.
use derive_more::Constructor;
use hash_utils::store::Store;

use crate::{
    environment::{
        context::Decl,
        env::{AccessToEnv, Env},
    },
    impl_access_to_env,
    mods::ModDefId,
    scopes::{Stack, StackId, StackMember, StackMemberData},
};

/// Operations related to the stack.
#[derive(Constructor)]
pub struct StackUtils<'tc> {
    env: &'tc Env<'tc>,
}

impl_access_to_env!(StackUtils<'tc>);

impl<'tc> StackUtils<'tc> {
    /// Create a new empty stack.
    pub fn create_stack(&self) -> StackId {
        self.stores().stack().create_with(|id| Stack { id, members: vec![], local_mod_def: None })
    }

    /// Set the local mod def of the given stack.
    pub fn set_local_mod_def(&self, stack_id: StackId, local_mod_def_id: ModDefId) {
        self.stores().stack().modify_fast(stack_id, |stack| {
            stack.local_mod_def = Some(local_mod_def_id);
        })
    }

    /// Set the members of the given stack.
    pub fn set_stack_members(&self, stack_id: StackId, members: impl IntoIterator<Item = Decl>) {
        self.stores().stack().modify_fast(stack_id, |stack| {
            stack.members.clear();
            stack.members.extend(members);
        })
    }

    /// Create stack members from the given iterator, for the given stack.
    pub fn create_stack_members<I: IntoIterator<Item = StackMemberData>>(
        &self,
        stack_id: StackId,
        data: I,
    ) -> impl IntoIterator<Item = StackMember>
    where
        I::IntoIter: ExactSizeIterator,
    {
        data.into_iter().enumerate().map(move |(index, data)| StackMember {
            id: (stack_id, index),
            is_mutable: data.is_mutable,
            name: data.name,
            ty: data.ty,
        })
    }
}
