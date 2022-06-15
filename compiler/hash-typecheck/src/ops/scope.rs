use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{Member, TyId, Value, ValueId, Var},
        scope::ScopeStack,
        AccessToStorage, StorageRefMut,
    },
};
use hash_source::identifier::Identifier;

use super::unify::Unifier;

pub struct SymbolResolver<'gs, 'ls, 'cd> {
    storage: StorageRefMut<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> SymbolResolver<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    fn unifier(&mut self) -> Unifier {
        Unifier::new(StorageRefMut {
            local_storage: self.storage.local_storage,
            global_storage: self.storage.global_storage,
            core_defs: self.storage.core_defs,
        })
    }

    pub fn resolve_var_ty(&mut self, var: &Var) -> TcResult<TyId> {
        let value_id = self.resolve_var_value(var)?;
        self.unifier().ty_of_value(value_id)
    }

    fn resolve_member_by_single_name_in_stack(
        &self,
        name: Identifier,
        scopes: &ScopeStack,
    ) -> Option<&Member> {
        for scope_id in scopes.iter_up() {
            let scope_value = self.storage.scope_store().get(scope_id);
            if let Some(member) = scope_value.get(name) {
                return Some(member);
            }
        }
        None
    }

    pub fn resolve_var_value(&mut self, var: &Var) -> TcResult<ValueId> {
        let mut last_scope = self.storage.scopes().to_owned();
        let mut names_iter = var.names.iter().enumerate().peekable();

        loop {
            match names_iter.next() {
                Some((_, &name)) => {
                    match self.resolve_member_by_single_name_in_stack(name, &last_scope) {
                        Some(member) => {
                            let value = member.value;
                            let simplified_value =
                                self.unifier().simplify_value(value)?.unwrap_or(value);
                            match self.storage.value_store().get(simplified_value) {
                                Value::ModDef(mod_def_id) if names_iter.peek().is_some() => {
                                    let mod_def = self.storage.mod_def_store().get(*mod_def_id);
                                    last_scope = ScopeStack::singular(mod_def.members);
                                }
                                _ if names_iter.peek().is_some() => {
                                    return Err(TcError::TryingToNamespaceValue(simplified_value));
                                }
                                _ => return Ok(simplified_value),
                            }
                        }
                        None => return Err(TcError::UnresolvedSymbol(name)),
                    }
                }
                None => unreachable!(),
            }
        }
    }
}
