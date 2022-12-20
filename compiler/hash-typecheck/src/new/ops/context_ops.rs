use derive_more::Constructor;
use hash_types::new::{
    environment::{
        context::{Binding, BindingKind, ScopeKind},
        env::AccessToEnv,
    },
    symbols::Symbol,
};
use hash_utils::store::Store;

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
    /// This will add all the scope bindings to the context, unless the scope
    /// is a stack scope, in which case the bindings should be added to the
    /// context using [`ContextOps::add_stack_binding()`].
    pub fn enter_scope<T>(&self, _kind: ScopeKind, _f: impl FnOnce() -> T) -> T {
        todo!()
    }

    /// Add a new stack binding to the current scope context.
    ///
    /// *Invariant*: It must be that the current scope is a stack scope,
    /// containing a member with the given name.
    pub fn add_stack_binding(&self, name: Symbol) {
        match self.context().get_scope_kind() {
            ScopeKind::Stack(stack_id) => {
                let member_id = self.stores().stack().map_fast(stack_id, |stack| {
                    stack.members.iter().find(|member| member.name == name).map(|member| member.id).unwrap_or_else(
                        || {
                            panic!(
                                "add_stack_binding called with non-existent member name '{}' on stack {}",
                                self.env().with(name), self.env().with(stack)
                            )
                        },
                    )
                });

                self.context()
                    .add_binding(Binding { name, kind: BindingKind::StackMember(member_id.into()) })
            }
            _ => panic!("add_stack_binding called in non-stack scope"),
        }
    }
}
