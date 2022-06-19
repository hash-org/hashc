//! Contains utilities to validate terms.
use crate::{
    error::TcResult,
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
        todo!()
    }

    /// Validate the trait definition of the given [TrtDefId]
    pub fn validate_trt_def(&mut self, _trt_def_id: TrtDefId) -> TcResult<()> {
        todo!()
    }

    /// Validate the nominal definition of the given [NominalDefId]
    pub fn validate_nominal_def(&mut self, _nominal_def_id: NominalDefId) -> TcResult<()> {
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
        //
        // @@Todo: actually implement these checks:
        match term {
            Term::Merge(_) => {
                // Validate each inner term.
                // Ensure all elements of the merge are not type functions, and are of the same level.
                todo!()
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
    pub fn subs_are_equivalent(&mut self, _s0: &Sub, _s1: &Sub) -> TcResult<bool> {
        todo!()
    }
}
