// @@Docs
use derive_more::Constructor;
use hash_types::new::{
    defs::DefMemberData,
    environment::env::AccessToEnv,
    scopes::{Stack, StackId, StackMember},
};
use hash_utils::store::Store;

use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

/// Operations related to the stack.
#[derive(Constructor)]
pub struct StackOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(StackOps<'tc>);

impl<'tc> StackOps<'tc> {
    /// Create a new empty stack.
    pub fn create_stack(&self) -> StackId {
        self.stores().stack().create_with(|id| Stack { id, members: vec![] })
    }

    /// Set the members of the given stack.
    pub fn set_stack_members(
        &self,
        stack_id: StackId,
        members: impl IntoIterator<Item = StackMember>,
    ) {
        self.stores().stack().modify_fast(stack_id, |stack| {
            stack.members.clear();
            stack.members.extend(members);
        })
    }

    /// Create stack members from the given iterator of members where the `bool`
    /// flag determines mutability.
    pub fn create_stack_members_from_def_members<I: IntoIterator<Item = (bool, DefMemberData)>>(
        &self,
        stack_id: StackId,
        data: I,
    ) -> impl IntoIterator<Item = StackMember>
    where
        I::IntoIter: ExactSizeIterator,
    {
        data.into_iter().enumerate().map(move |(index, (is_mutable, data))| StackMember {
            id: (stack_id, index),
            is_mutable,
            name: data.name,
            ty: data.ty,
            value: data.value,
        })
    }
}
