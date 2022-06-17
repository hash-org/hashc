//! Contains functionality to simplify terms into more concrete terms.

// @@Remove
#![allow(unused)]

use super::unify::Unifier;
use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{AccessTerm, AppTyFn, Member, Term, TermId},
        scope::ScopeStack,
        AccessToStorage, AccessToStorageMut, StorageRefMut,
    },
};
use hash_source::identifier::Identifier;

/// Can resolve the type of a given term, as another term.
pub struct Simplifier<'gs, 'ls, 'cd> {
    storage: StorageRefMut<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for Simplifier<'gs, 'ls, 'cd> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> AccessToStorageMut for Simplifier<'gs, 'ls, 'cd> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd> Simplifier<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    /// Convenience method to get a [Unifier].
    fn unifier(&mut self) -> Unifier {
        Unifier::new(self.storages_mut())
    }

    /// Resolve the given name in the given [ScopeStack], if found.
    ///
    /// This does not recurse into children members, since the name is just a single identifier
    /// rather than an [AccessTerm](crate::storage::primitives::AccessTerm).
    fn _resolve_name_in_scopes(&self, name: Identifier, scopes: &ScopeStack) -> Option<Member> {
        let reader = self.reader();
        for scope_id in scopes.iter_up() {
            if let Some(member) = reader.get_scope(scope_id).get(name) {
                return Some(member);
            }
        }
        None
    }

    /// Apply the given access term structure.
    fn _apply_access_term(&mut self, access_term: &AccessTerm) -> TcResult<Option<Member>> {
        let _simplified_subject = self.unifier();
        let subject = self.reader().get_term(access_term.subject_id).clone();

        match subject {
            Term::Access(_) => todo!(),
            Term::Var(_) => todo!(),
            Term::Merge(_) => todo!(),
            Term::TyFn(_) => todo!(),
            Term::TyFnTy(_) => todo!(),
            Term::AppTyFn(_) => todo!(),
            Term::AppSub(_) => todo!(),
            Term::Unresolved(_) => todo!(),
            Term::Level3(_) => todo!(),
            Term::Level2(_) => todo!(),
            Term::Level1(_) => todo!(),
            Term::Level0(_) => todo!(),
        }

        todo!()
    }

    /// Apply the given type function application structure.
    fn apply_ty_fn(&mut self, apply_ty_fn: &AppTyFn) -> TcResult<Option<TermId>> {
        let subject_id = self
            .simplify_term(apply_ty_fn.subject)?
            .unwrap_or(apply_ty_fn.subject);
        let subject = self.storage.term_store().get(subject_id);
        match subject {
            Term::TyFn(_) => {
                todo!()
            }
            Term::AppTyFn(inner_apply_ty_fn) => {
                let inner_apply_ty_fn = inner_apply_ty_fn.clone();
                // Recurse
                let inner_apply_ty_fn_result_id = self.apply_ty_fn(&inner_apply_ty_fn)?;
                match inner_apply_ty_fn_result_id {
                    Some(inner_apply_ty_fn_result_id) => {
                        match self.storage.term_store().get(inner_apply_ty_fn_result_id) {
                            Term::TyFn(_) => self.apply_ty_fn(&AppTyFn {
                                subject: inner_apply_ty_fn_result_id,
                                args: apply_ty_fn.args.clone(),
                            }),
                            _ => Err(TcError::NotATypeFunction(subject_id)),
                        }
                    }
                    None => Ok(None),
                }
            }
            _ => Err(TcError::NotATypeFunction(subject_id)),
        }
    }

    /// Simplify the given term, just returning the original if no simplification occurred.
    pub fn potentially_simplify_term(&mut self, term_id: TermId) -> TcResult<TermId> {
        Ok(self.simplify_term(term_id)?.unwrap_or(term_id))
    }

    /// Simplify the given term.
    pub fn simplify_term(&mut self, value_id: TermId) -> TcResult<Option<TermId>> {
        let value = self.storage.term_store().get(value_id);
        match value {
            Term::AppTyFn(apply_ty_fn) => {
                let apply_ty_fn = apply_ty_fn.clone();
                let result = self.apply_ty_fn(&apply_ty_fn)?;
                match result {
                    Some(result) => Ok(Some(result)),
                    None => Ok(None),
                }
            }
            Term::Merge(inner) => {
                let inner = inner.clone();
                let inner_tys = inner
                    .iter()
                    .map(|&ty| self.simplify_term(ty))
                    .collect::<Result<Vec<_>, _>>()?;
                if inner_tys.iter().any(|x| x.is_some()) {
                    Ok(Some(
                        self.builder().create_merge_term(
                            inner_tys
                                .iter()
                                .zip(inner)
                                .map(|(new, old)| new.unwrap_or(old)),
                        ),
                    ))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }
}
