//! Contains utilities to validate terms.
use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{FnTy, Level1Term, ModDefId, NominalDefId, Sub, Term, TermId, TrtDefId},
        AccessToStorage, AccessToStorageMut, StorageRefMut,
    },
};

use super::{AccessToOps, AccessToOpsMut};

/// Represents the level of a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TermLevel {
    Level0,
    Level1,
    Level2,
    Level3,
}

/// Can resolve the type of a given term, as another term.
pub struct Validator<'gs, 'ls, 'cd> {
    storage: StorageRefMut<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for Validator<'gs, 'ls, 'cd> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> AccessToStorageMut for Validator<'gs, 'ls, 'cd> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

/// Used to communicate the result of a successful term validation, which produces the simplified
/// term as well as its type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TermValidation {
    pub simplified_term_id: TermId,
    pub term_ty_id: TermId,
}

impl<'gs, 'ls, 'cd> Validator<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    /// Validate the module definition of the given [ModDefId]
    pub fn validate_mod_def(&mut self, _mod_def_id: ModDefId) -> TcResult<()> {
        // Ensure if it is a trait impl it implements all the trait members.
        todo!()
    }

    /// Validate the trait definition of the given [TrtDefId]
    pub fn validate_trt_def(&mut self, _trt_def_id: TrtDefId) -> TcResult<()> {
        // Ensure Self exists?
        // @@Design: do we allow traits without self?
        todo!()
    }

    /// Validate the nominal definition of the given [NominalDefId]
    pub fn validate_nominal_def(&mut self, _nominal_def_id: NominalDefId) -> TcResult<()> {
        // Ensure all members have level 1 types/level 0 default values and the default values are
        // of the given type.
        todo!()
    }

    /// Validate the given term for correctness.
    ///
    /// Returns the simplified term, along with its type, which are computed during the validation.
    pub fn validate_term(&mut self, term_id: TermId) -> TcResult<TermValidation> {
        // First, we try simplify the term:
        let simplified_term_id = self.simplifier().potentially_simplify_term(term_id)?;

        // Then, we try get its type:
        let term_ty_id = self.typer().ty_of_simplified_term(simplified_term_id)?;

        // If both of these succeeded, we can perform a few final checks:
        let reader = self.reader();

        // Prepare the result of the validation:
        let result = TermValidation {
            simplified_term_id,
            term_ty_id,
        };

        let term = reader.get_term(simplified_term_id);
        // @@PotentiallyIncomplete: there might are a few more checks we need to perform here, but
        // this is not yet evident.
        match term {
            Term::Merge(terms) => {
                // First, validate each term:
                let terms = terms.clone();
                for term in terms.iter().copied() {
                    self.validate_term(term)?;
                }

                // Ensure all elements of the merge are either Level 2, or all Level 1.
                // Furthermore, if they are level 1, they should only have zero or one nominal
                // definition attached.
                enum MergeKind {
                    Unknown,
                    Level2,
                    Level1 { nominal_attached: Option<TermId> },
                }
                let mut merge_kind = MergeKind::Unknown;
                for term_id in terms.iter().copied() {
                    let reader = self.reader();
                    let term = reader.get_term(term_id);
                    match term {
                        Term::Level2(_) => todo!(),
                        Term::Access(_) => todo!(),
                        Term::Var(_) => todo!(),
                        Term::Merge(_) => todo!(),
                        Term::TyFn(_) => todo!(),
                        Term::TyFnTy(_) => todo!(),
                        Term::AppTyFn(_) => todo!(),
                        Term::AppSub(_) => todo!(),
                        Term::Unresolved(_) => todo!(),
                        Term::Level3(_) => todo!(),
                        Term::Level1(_) => todo!(),
                        Term::Level0(_) => todo!(),
                        _ => return Err(TcError::InvalidElementOfMerge { term: term_id }),
                    }
                }

                Ok(result)
            }
            Term::TyFn(_) => {
                // Validate each member.
                // Ensure the return value of each case is a subtype of the general return type.
                todo!()
            }
            Term::Level1(level1_term) => match level1_term {
                Level1Term::Tuple(_) => {
                    // Validate each parameter
                    todo!()
                }
                Level1Term::Fn(_) => {
                    // Validate parameters and return type
                    todo!()
                }
                Level1Term::ModDef(_) | Level1Term::NominalDef(_) => {
                    // Nothing to do
                    Ok(result)
                }
            },
            Term::Level0(_) => {
                // Validate the inner type and ensure it is level 1
                todo!()
            }
            Term::Level2(_)
            | Term::Level3(_)
            | Term::Access(_)
            | Term::Var(_)
            | Term::AppSub(_)
            | Term::TyFnTy(_)
            | Term::AppTyFn(_)
            | Term::Unresolved(_) => {
                // Nothing to do, should have already been validated by the typer.
                Ok(result)
            }
        }
    }

    /// Determine whether the given term is constant, i.e. has no side effects.
    ///
    /// This is the condition for the term to be able to be used as the return type of a type
    /// function, or to be used in global scope.
    pub fn term_is_constant(&mut self, term_id: TermId) -> TcResult<bool> {
        // Make sure the term is valid first:
        self.validate_term(term_id)?;
        let simplified_term_id = self.simplifier().potentially_simplify_term(term_id)?;
        let reader = self.reader();
        let term = reader.get_term(simplified_term_id);
        // @@Todo: actually implement this:
        match term {
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
    }

    /// Determine if the given term is a function type, and if so return it.
    pub fn term_is_fn_ty(&mut self, term_id: TermId) -> TcResult<Option<FnTy>> {
        let simplified_term_id = self.simplifier().potentially_simplify_term(term_id)?;
        let reader = self.reader();
        let term = reader.get_term(simplified_term_id);
        match term {
            Term::Level1(Level1Term::Fn(fn_ty)) => Ok(Some(fn_ty.clone())),
            _ => Ok(None),
        }
    }

    /// Determine if the two given substitutions are equivalent.
    ///
    /// That is, if for any term X, they produce the same result when applied to X
    ///
    /// @@Correctness: This is not based on any accepted algorithm, and requires testing to ensure
    /// its correctness.
    pub fn subs_are_equivalent(&mut self, s0: &Sub, s1: &Sub) -> bool {
        // First we get the two substitutions as lists sorted by their domains:
        let mut s0_list = s0.pairs().collect::<Vec<_>>();
        let mut s1_list = s1.pairs().collect::<Vec<_>>();
        s0_list.sort_by_key(|x| x.0);
        s1_list.sort_by_key(|x| x.0);

        // Then for each pair, we ensure the domain elements are the same, and the range elements
        // can be unified:
        for (s0_element, s1_element) in s0_list.iter().zip(&s1_list) {
            if s0_element.0 != s1_element.0 {
                return false;
            }

            // Unify bidirectionally
            if self
                .unifier()
                .unify_terms(s0_element.1, s1_element.1)
                .is_err()
                || self
                    .unifier()
                    .unify_terms(s1_element.1, s0_element.1)
                    .is_err()
            {
                return false;
            }
        }

        // If all succeeded, the substitutions are equivalent!
        true
    }
}
