#![allow(unused)]

use crate::{
    error::TcResult,
    storage::{
        primitives::{Member, ScopeId, TermId, Var},
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

    pub fn resolve_name_in_value_get_value(
        &mut self,
        _name: Identifier,
        _value_id: TermId,
    ) -> TcResult<TermId> {
        todo!()
        // let simplified_value_id = self.unifier().potentially_simplify_value(value_id)?;
        // let invalid_access = || -> TcResult<TermId> {
        //     Err(TcError::TryingToNamespaceNonNamespaceable(
        //         simplified_value_id,
        //     ))
        // };

        // match self.storage.value_store().get(simplified_value_id) {
        //     Term::Trt(_) => {
        //         invalid_access()
        //     }
        //     Term::Ty(_) => invalid_access(),
        //     Term::Rt(_) => invalid_access(),
        //     Term::TyFn(_) => invalid_access(),
        //     Term::Unset(_) => {
        //         // Forward the unset to an unset value of the resultant type?
        //         todo!()
        //     },
        //     Term::AppTyFn(_) => {
        //         // We already tried initially to simplify it, all we can do now is wrap it in an
        //         // Access(..) and hope it will be simplified once more type vars are substituted
        //         // for concrete types

        //         // But we first have to ensure the trait actually has the thing

        //         todo!()
        //     }
        //     Term::Mod(_) => todo!(),
        //     Term::Nominal(_) => todo!(),
        //     Term::Var(_) => todo!(),
        //     Term::EnumVariant(_) => todo!(),
        //     Term::Merge(_) => {
        //         // If there are multiple results here we want to error that it is ambiguous
        //         todo!()
        //     }
        //     Term::Access(_) => todo!(),
        // }
    }

    pub fn resolve_var_in_scopes(&mut self, _var: &Var) -> TcResult<TermId> {
        let _last_scope = self.storage.scopes().to_owned();
        // let mut names_iter = var.iter().enumerate().peekable();

        todo!()
        // loop {
        //     match names_iter.next() {
        //         Some((_, &name)) => {
        //             match self.resolve_name_in_scopes_get_member(name, &last_scope) {
        //                 Some(member) => {
        //                     let resolved =
        //                         self.resolve_name_in_value_get_value(name, member.value)?;
        //                     match self.storage.value_store().get(resolved) {
        //                         Term::Mod(mod_def_id) if names_iter.peek().is_some() => {
        //                             let mod_def = self.storage.mod_def_store().get(*mod_def_id);
        //                             last_scope = ScopeStack::singular(mod_def.members);
        //                         }
        //                         _ if names_iter.peek().is_some() => {
        //                             return Err(TcError::TryingToNamespaceNonNamespaceable(
        //                                 resolved,
        //                             ));
        //                         }
        //                         _ => return Ok(resolved),
        //                     }
        //                 }
        //                 None => return Err(TcError::UnresolvedSymbol(name)),
        //             }
        //         }
        //         None => unreachable!(),
        //     }
        // }
    }
}
