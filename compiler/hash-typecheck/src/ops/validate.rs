//! Contains utilities to validate terms.
use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{
            FnTy, Level1Term, Level2Term, ModDefId, NominalDefId, Params, Sub, Term, TermId,
            TrtDefId,
        },
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

/// Helper type for [Validator::validate_merge_element], to keep track of the kind of the merge
/// (whether it is level 2, level 1, or not known yet).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MergeKind {
    Unknown,
    Level2,
    Level1 { nominal_attached: Option<TermId> },
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

    /// Ensure the element `merge_element_term_id` of the merge with the given `merge_term_id` is
    /// either level 2 (along with the merge being all level 2), or level 1 (along with the merge
    /// being all level 1). Furthermore, if it is level 1, the merge should only have zero or one
    /// nominal definition attached.
    fn validate_merge_element(
        &mut self,
        merge_kind: &mut MergeKind,
        merge_term_id: TermId,
        merge_element_term_id: TermId,
    ) -> TcResult<()> {
        let reader = self.reader();
        let merge_element_term = reader.get_term(merge_element_term_id);

        // Error helper:
        let invalid_merge_element = || -> TcResult<()> {
            Err(TcError::InvalidElementOfMerge {
                term: merge_element_term_id,
            })
        };

        // Helper to ensure that a merge is level 2
        let mut ensure_merge_is_level2 = || {
            match merge_kind {
                MergeKind::Unknown => {
                    // Now we know that the merge should be level 2
                    *merge_kind = MergeKind::Level2;
                    Ok(())
                }
                MergeKind::Level2 => {
                    // Merge is already level 2, all good:
                    Ok(())
                }
                MergeKind::Level1 {
                    nominal_attached: _,
                } => {
                    // Merge was already specified to be level 1, error!
                    Err(TcError::MergeShouldBeLevel2 {
                        merge_term: merge_term_id,
                        offending_term: merge_element_term_id,
                    })
                }
            }
        };

        // Ensure the level of the term is valid:
        match merge_element_term {
            Term::Access(_) => todo!(),
            Term::Var(_) => todo!(),
            Term::TyFn(_) => todo!(),
            Term::TyFnTy(_) => todo!(),
            // Type function application:
            // This should have already been simplified, so we only accept it if its type is level
            // 3 and the merge is level 2, which means it is a level 2 term. If its type is level
            // 2, we cannot be sure it won't have a duplicate nominal definition so we cannot
            // accept it.
            Term::AppTyFn(_) => {
                let ty_id_of_term = self.typer().ty_of_term(merge_element_term_id)?;
                let reader = self.reader();
                let ty_of_term = reader.get_term(ty_id_of_term);
                match ty_of_term {
                    Term::Level3(_) => {
                        // If the type of the term is level 3, then we know that the merge should be level 2:
                        ensure_merge_is_level2()
                    }
                    _ => {
                        // @@ErrorReporting: we could add a more descriptive message here.
                        invalid_merge_element()
                    }
                }
            }
            Term::AppSub(app_sub) => {
                // Ensure the inner one is valid, substitution doesn't matter:
                self.validate_merge_element(merge_kind, merge_term_id, app_sub.term)
            }
            // Unclear if this fits the requirements, so we reject it:
            Term::Unresolved(_) => {
                // @@ErrorReporting: we could hint to add more type annotations.
                invalid_merge_element()
            }
            // Level 3 terms are not allowed:
            Term::Level3(_) => invalid_merge_element(),
            // Level 2 terms are allowed:
            Term::Level2(level2_term) => match level2_term {
                Level2Term::Trt(_) | Level2Term::AnyTy => ensure_merge_is_level2(),
            },
            // Level 1 terms are allowed:
            Term::Level1(level1_term) => match level1_term {
                // Modules:
                Level1Term::ModDef(_) => match merge_kind {
                    MergeKind::Unknown => {
                        // Now we know that the merge should be level 1
                        *merge_kind = MergeKind::Level1 {
                            nominal_attached: None,
                        };
                        Ok(())
                    }
                    MergeKind::Level2 => {
                        // Merge was already specified to be level 2, error!
                        Err(TcError::MergeShouldBeLevel1 {
                            merge_term: merge_term_id,
                            offending_term: merge_element_term_id,
                        })
                    }
                    MergeKind::Level1 {
                        nominal_attached: _,
                    } => {
                        // Merge is level 1; independently of whether a nominal is
                        // attached, this is fine.
                        Ok(())
                    }
                },
                // Nominals:
                Level1Term::NominalDef(_) => match merge_kind {
                    MergeKind::Unknown
                    | MergeKind::Level1 {
                        nominal_attached: None,
                    } => {
                        // Merge is either unknown, or level 1 without a nominal; we attach the nominal.
                        *merge_kind = MergeKind::Level1 {
                            nominal_attached: Some(merge_element_term_id),
                        };
                        Ok(())
                    }
                    MergeKind::Level2 => {
                        // Merge was already specified to be level 2, error!
                        Err(TcError::MergeShouldBeLevel1 {
                            merge_term: merge_term_id,
                            offending_term: merge_element_term_id,
                        })
                    }
                    MergeKind::Level1 {
                        nominal_attached: Some(nominal_term_id),
                    } => {
                        // A nominal has already been attached, error!
                        Err(TcError::MergeShouldOnlyContainOneNominal {
                            merge_term: merge_term_id,
                            nominal_term: *nominal_term_id,
                            second_nominal_term: merge_element_term_id,
                        })
                    }
                },
                // Cannot attach a tuple to a merge
                // @@Design: can we possibly allow this?
                Level1Term::Tuple(_) => invalid_merge_element(),
                // Cannot attach a function type to a merge
                Level1Term::Fn(_) => invalid_merge_element(),
            },
            // Level 0 elements are not allowed
            Term::Level0(_) => invalid_merge_element(),
            // Root is not allowed
            Term::Root => invalid_merge_element(),
            // This should have been flattened already:
            Term::Merge(_) => {
                unreachable!("Merge term should have already been flattened")
            }
        }
    }

    /// Validate the given parameters, by validating their types and values.
    pub fn validate_params(&mut self, params: &Params) -> TcResult<()> {
        for param in params.positional() {
            self.validate_term(param.ty)?;
            if let Some(default_value) = param.default_value {
                self.validate_term(default_value)?;
            }
        }
        Ok(())
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
            // Merge:
            Term::Merge(terms) => {
                // First, validate each term:
                let terms = terms.clone();
                for term in terms.iter().copied() {
                    self.validate_term(term)?;
                }

                // Validate the level of each term against the merge restrictions (see
                // [Self::validate_merge_element] docs).
                let mut merge_kind = MergeKind::Unknown;
                for merge_element_term_id in terms.iter().copied() {
                    self.validate_merge_element(
                        &mut merge_kind,
                        simplified_term_id,
                        merge_element_term_id,
                    )?;
                }

                // If both checks succeeded, merge is OK!
                Ok(result)
            }

            // Type function:
            Term::TyFn(ty_fn) => {
                // Validate params and return type.
                let ty_fn = ty_fn.clone();
                self.validate_params(&ty_fn.general_params)?;
                let general_return_validation = self.validate_term(ty_fn.general_return_ty)?;

                // Validate each case:
                for case in &ty_fn.cases {
                    self.validate_params(&case.params)?;
                    self.validate_term(case.return_ty)?;
                    self.validate_term(case.return_value)?;

                    // Ensure that the return type can be unified with the type of the return value:
                    // @@Safety: should be already simplified from above the match.
                    let return_value_ty = self.typer().ty_of_simplified_term(term_id)?;
                    let _ = self
                        .unifier()
                        .unify_terms(case.return_ty, return_value_ty)?;

                    // Ensure the return value of each case is a subtype of the general return type.
                    let _ = self
                        .unifier()
                        .unify_terms(case.return_ty, general_return_validation.term_ty_id)?;
                }

                // All checks succeeded, type function is OK!
                Ok(result)
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
            | Term::Root
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
            Term::Root => todo!(),
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
