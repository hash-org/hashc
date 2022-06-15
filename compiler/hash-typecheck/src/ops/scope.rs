use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{Member, ScopeId, Ty, TyId, Value, ValueId, Var},
        scope::ScopeStack,
        AccessToStorage, AccessToStorageMut, StorageRefMut,
    },
};
use hash_source::identifier::Identifier;

use super::{building::PrimitiveBuilder, unify::Unifier};

pub struct SymbolResolver<'gs, 'ls, 'cd> {
    storage: StorageRefMut<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> SymbolResolver<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    fn unifier(&mut self) -> Unifier {
        Unifier::new(self.storage.storages_mut())
    }

    fn primitive_builder(&mut self) -> PrimitiveBuilder {
        PrimitiveBuilder::new(self.storage.global_storage_mut())
    }

    pub fn resolve_var_ty(&mut self, var: &Var) -> TcResult<TyId> {
        let value_id = self.resolve_var_in_scopes(var)?;
        self.unifier().ty_of_value(value_id)
    }

    fn resolve_name_in_scopes_get_member(
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

    pub fn resolve_name_in_scope(&self, name: Identifier, scope_id: ScopeId) -> Option<&Member> {
        let scope = self.storage.scope_store().get(scope_id);
        scope.get(name)
    }

    pub fn name_exists_in_unset_value_of_type(
        &mut self,
        name: Identifier,
        ty_id: TyId,
    ) -> TcResult<bool> {
        let simplified_ty_id = self.unifier().potentially_simplify_ty(ty_id)?;
        let unset_value_id = self.primitive_builder().create_unset_value(ty_id);
        let invalid_access = || -> TcResult<bool> {
            Err(TcError::TryingToNamespaceNonNamespaceable(unset_value_id))
        };

        match self.storage.ty_store().get(simplified_ty_id) {
            Ty::Ty(Some(trt_def_id)) => {
                let trt_def = self.storage.trt_def_store().get(*trt_def_id);
                Ok(self.resolve_name_in_scope(name, trt_def.members).is_some())
            }
            Ty::AppTyFn(_) => {
                // Get return ty of the app ty fn (substituted) and check if the result has the
                // member
                todo!()
            }
            Ty::Ty(None) => invalid_access(),
            Ty::TyFn(_) => invalid_access(),
            Ty::Trt => todo!(),
            Ty::NominalDef(_) => todo!(),
            Ty::ModDef(_) => todo!(),
            Ty::Tuple(_) => todo!(),
            Ty::Fn(_) => todo!(),
            Ty::Var(_) => todo!(),
            Ty::Merge(_) => todo!(),
            Ty::Unresolved(_) => {
                // @@Future: room for crazy type inference here
                invalid_access()
            }
        }
    }

    pub fn resolve_name_in_value_get_value(
        &mut self,
        _name: Identifier,
        value_id: ValueId,
    ) -> TcResult<ValueId> {
        let simplified_value_id = self.unifier().potentially_simplify_value(value_id)?;
        let invalid_access = || -> TcResult<ValueId> {
            Err(TcError::TryingToNamespaceNonNamespaceable(
                simplified_value_id,
            ))
        };

        match self.storage.value_store().get(simplified_value_id) {
            Value::Trt(_) => {
                invalid_access()
            }
            Value::Ty(_) => invalid_access(),
            Value::Rt(_) => invalid_access(),
            Value::TyFn(_) => invalid_access(),
            Value::Unset(_) => {
                // Forward the unset to an unset value of the resultant type?
                todo!()
            },
            Value::AppTyFn(_) => {
                // We already tried initially to simplify it, all we can do now is wrap it in an
                // Access(..) and hope it will be simplified once more type vars are substituted
                // for concrete types

                // But we first have to ensure the trait actually has the thing

                todo!()
            }
            Value::ModDef(_) => todo!(),
            Value::NominalDef(_) => todo!(),
            Value::Var(_) => todo!(),
            Value::EnumVariant(_) => todo!(),
            Value::Merge(_) => {
                // If there are multiple results here we want to error that it is ambiguous
                todo!()
            }
            Value::Access(_) => todo!(),
        }
    }

    pub fn resolve_var_in_scopes(&mut self, var: &Var) -> TcResult<ValueId> {
        let mut last_scope = self.storage.scopes().to_owned();
        let mut names_iter = var.names.iter().enumerate().peekable();

        loop {
            match names_iter.next() {
                Some((_, &name)) => {
                    match self.resolve_name_in_scopes_get_member(name, &last_scope) {
                        Some(member) => {
                            let resolved =
                                self.resolve_name_in_value_get_value(name, member.value)?;
                            match self.storage.value_store().get(resolved) {
                                Value::ModDef(mod_def_id) if names_iter.peek().is_some() => {
                                    let mod_def = self.storage.mod_def_store().get(*mod_def_id);
                                    last_scope = ScopeStack::singular(mod_def.members);
                                }
                                _ if names_iter.peek().is_some() => {
                                    return Err(TcError::TryingToNamespaceNonNamespaceable(
                                        resolved,
                                    ));
                                }
                                _ => return Ok(resolved),
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
