//! Contains functionality to simplify terms into more concrete terms.

// @@Remove
#![allow(unused)]

use super::{substitute::Substituter, unify::Unifier};
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

    /// Convenience method to get a [Substituter].
    fn substituter(&mut self) -> Substituter {
        Substituter::new(self.storages_mut())
    }

    /// Resolve the given name in the given [ScopeStack], if found.
    ///
    /// This does not recurse into children members, since the name is just a single identifier
    /// rather than an [AccessTerm](crate::storage::primitives::AccessTerm).
    fn resolve_name_in_scopes(&self, name: Identifier, scopes: &ScopeStack) -> Option<Member> {
        let reader = self.reader();
        for scope_id in scopes.iter_up() {
            if let Some(member) = reader.get_scope(scope_id).get(name) {
                return Some(member);
            }
        }
        None
    }

    /// Apply the given access term structure, if possible.
    fn apply_access_term(&mut self, access_term: &AccessTerm) -> TcResult<Option<TermId>> {
        let simplified_subject = self.potentially_simplify_term(access_term.subject_id)?;
        let subject = self.reader().get_term(simplified_subject).clone();
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

    /// Apply the given type function application structure, if possible.
    fn apply_ty_fn(&mut self, apply_ty_fn: &AppTyFn) -> TcResult<Option<TermId>> {
        let simplified_subject_id = self.potentially_simplify_term(apply_ty_fn.subject)?;
        let simplified_subject = self.reader().get_term(simplified_subject_id).clone();
        match simplified_subject {
            Term::TyFn(_) => {
                todo!()
            }
            _ => Ok(None),
        }
    }

    /// Simplify the given term, just returning the original if no simplification occurred.
    pub fn potentially_simplify_term(&mut self, term_id: TermId) -> TcResult<TermId> {
        Ok(self.simplify_term(term_id)?.unwrap_or(term_id))
    }

    /// Simplify the given term, if possible.
    pub fn simplify_term(&mut self, term_id: TermId) -> TcResult<Option<TermId>> {
        let value = self.reader().get_term(term_id).clone();
        match value {
            Term::Merge(inner) => {
                /// Simplify each element of the merge:
                let inner = inner.clone();
                let inner_tys = inner
                    .iter()
                    .map(|&ty| self.simplify_term(ty))
                    .collect::<Result<Vec<_>, _>>()?;

                if inner_tys.iter().any(|x| x.is_some()) {
                    // If any of them have been simplified, create a new term
                    Ok(Some(
                        self.builder().create_merge_term(
                            inner_tys
                                .iter()
                                .zip(inner)
                                .map(|(new, old)| new.unwrap_or(old)),
                        ),
                    ))
                } else {
                    // No simplification occurred
                    Ok(None)
                }
            }
            // Recurse:
            Term::AppSub(apply_sub) => Ok(Some(
                /// @@Performance: add Option<_> to the substituter to return terms which don't
                /// have the variables in them.
                self.substituter()
                    .apply_sub_to_term(&apply_sub.sub, apply_sub.term),
            )),
            Term::AppTyFn(apply_ty_fn) => self.apply_ty_fn(&apply_ty_fn),
            Term::Access(access_term) => self.apply_access_term(&access_term),
            // Cannot simplify:
            //
            // @@Future: we might wanna simplify inner terms here?
            Term::TyFn(_)
            | Term::TyFnTy(_)
            | Term::Unresolved(_)
            | Term::Var(_)
            | Term::Level3(_)
            | Term::Level2(_)
            | Term::Level1(_)
            | Term::Level0(_) => Ok(None),
        }
    }
}
