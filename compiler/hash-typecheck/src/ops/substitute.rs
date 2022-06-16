//! Functionality related to variable substitution inside terms/types.
use crate::{
    error::TcResult,
    storage::{
        primitives::{
            AppTyFn, Arg, Args, Level0Term, Level1Term, Level2Term, Level3Term, Param, ParamList,
            Params, Term, TermId, TyFn, TyFnCase, TyFnTy, UnresolvedTerm, Var,
        },
        AccessToStorage, AccessToStorageMut, StorageRefMut,
    },
};
use std::collections::HashMap;

/// The subject of a substitution, either a type variable or an unresolved type.
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum SubSubject {
    Var(Var),
    Unresolved(UnresolvedTerm),
}

impl From<Var> for SubSubject {
    fn from(var: Var) -> Self {
        SubSubject::Var(var)
    }
}

impl From<UnresolvedTerm> for SubSubject {
    fn from(unresolved: UnresolvedTerm) -> Self {
        SubSubject::Unresolved(unresolved)
    }
}

/// A substitution containing pairs of `(SubSubject, TermId)` to be applied to a type or types.
#[derive(Debug, Default, Clone)]
pub struct Sub {
    data: HashMap<SubSubject, TermId>,
}

impl Sub {
    /// Create an empty substitution.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Create a substitution from pairs of `(TySubSubject, TermId)`.
    pub fn from_pairs(pairs: impl IntoIterator<Item = (SubSubject, TermId)>) -> Self {
        Self {
            data: pairs.into_iter().collect(),
        }
    }

    /// Get the substitution for the given [SubSubject], if any.
    pub fn get_sub_for(&self, subject: SubSubject) -> Option<TermId> {
        self.data.get(&subject).copied()
    }

    /// Merge the substitution with another.
    ///
    /// Modifies `self`.
    pub fn merge_with(&mut self, _other: &Sub) {
        todo!()
    }
}

/// kkImplements equality of substitutions in terms of functional equality---will applying A produce
/// the same type as B?
///
/// @@Volatile: This might require having access to the storage to check equality of some things..
impl PartialEq for Sub {
    fn eq(&self, other: &Self) -> bool {
        // @@Todo: more sophisticated substitution equivalence
        self.data == other.data
    }
}

/// A judgement as to whether two values are equal, which also might be unclear (for example if
/// higher order type variables are involved).
pub enum TermsAreEqual {
    Yes,
    No,
    Unsure,
}

/// Can perform substitutions (see [Sub]) on terms.
pub struct Substitutor<'gs, 'ls, 'cd> {
    storage: StorageRefMut<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for Substitutor<'gs, 'ls, 'cd> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> AccessToStorageMut for Substitutor<'gs, 'ls, 'cd> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd> Substitutor<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    /// Apply the given substitution to the given arguments, producing a new set of arguments
    /// with the substituted variables.
    pub fn apply_sub_to_args(&mut self, sub: &Sub, args: &Args) -> TcResult<Args> {
        let new_args = args
            .positional()
            .iter()
            .map(|arg| {
                Ok(Arg {
                    name: arg.name,
                    value: self.apply_sub_to_term(sub, arg.value)?,
                })
            })
            .collect::<TcResult<Vec<_>>>()?;
        Ok(ParamList::new(new_args))
    }

    /// Apply the given substitution to the given parameters, producing a new set of parameters
    /// with the substituted variables.
    pub fn apply_sub_to_params(&mut self, sub: &Sub, params: &Params) -> TcResult<Params> {
        let new_params = params
            .positional()
            .iter()
            .map(|param| {
                Ok(Param {
                    name: param.name,
                    ty: self.apply_sub_to_term(sub, param.ty)?,
                    default_value: param
                        .default_value
                        .map(|value| self.apply_sub_to_term(sub, value))
                        .transpose()?,
                })
            })
            .collect::<TcResult<Vec<_>>>()?;
        Ok(ParamList::new(new_params))
    }

    /// Apply the given substitution to the given [Level3Term], producing a new [Level3Term] with
    /// the substituted variables.
    pub fn apply_sub_to_level3_term(&mut self, _: &Sub, term: Level3Term) -> TcResult<Level3Term> {
        match term {
            Level3Term::TrtKind => Ok(Level3Term::TrtKind),
        }
    }

    /// Apply the given substitution to the given [Level2Term], producing a new [Level2Term] with
    /// the substituted variables.
    pub fn apply_sub_to_level2_term(
        &mut self,
        _sub: &Sub,
        term: Level2Term,
    ) -> TcResult<Level2Term> {
        match term {
            Level2Term::Trt(_) => {
                todo!()
            }
            Level2Term::AnyTy => todo!(),
        }
    }

    /// Apply the given substitution to the given [Level1Term], producing a new [Level1Term] with
    /// the substituted variables.
    pub fn apply_sub_to_level1_term(
        &mut self,
        _sub: &Sub,
        _term: Level1Term,
    ) -> TcResult<Level1Term> {
        todo!()
    }

    /// Apply the given substitution to the given [Level0Term], producing a new [Level0Term] with
    /// the substituted variables.
    pub fn apply_sub_to_level0_term(
        &mut self,
        _sub: &Sub,
        _term: Level0Term,
    ) -> TcResult<Level0Term> {
        todo!()
    }

    /// Apply the given substitution to the term indexed by the given [TermId], producing a new
    /// term with the substituted variables.
    pub fn apply_sub_to_term(&mut self, sub: &Sub, term_id: TermId) -> TcResult<TermId> {
        // @@Performance: here we copy a lot, maybe there is a way to avoid all this copying by
        // first checking that the variables to be substituted actually exist in the term.

        let term = self.reader().get_term(term_id).clone();
        match term {
            Term::Access(access) => {
                // Just apply the substitution to the subject:
                let subbed_subject_id = self.apply_sub_to_term(sub, access.subject_id)?;
                Ok(self.builder().create_access(subbed_subject_id, access.name))
            }
            Term::Var(var) => {
                // If the variable is in the substitution, substitute it, otherwise do nothing.
                match sub.get_sub_for(var.into()) {
                    Some(subbed_term_id) => Ok(subbed_term_id),
                    None => Ok(term_id),
                }
            }
            Term::Merge(terms) => {
                // Apply the substitution to each element of the merge.
                let terms = terms
                    .into_iter()
                    .map(|term| self.apply_sub_to_term(sub, term))
                    .collect::<TcResult<Vec<_>>>()?;
                Ok(self.builder().create_term(Term::Merge(terms)))
            }
            Term::TyFn(ty_fn) => {
                // Apply the substitution to the general parameters, return type, and each case.
                let subbed_general_params = self.apply_sub_to_params(sub, &ty_fn.general_params)?;
                let subbed_general_return_ty =
                    self.apply_sub_to_term(sub, ty_fn.general_return_ty)?;
                let subbed_cases = ty_fn
                    .cases
                    .into_iter()
                    .map(|case| -> TcResult<_> {
                        Ok(TyFnCase {
                            params: self.apply_sub_to_params(sub, &case.params)?,
                            return_ty: self.apply_sub_to_term(sub, case.return_ty)?,
                            return_value: self.apply_sub_to_term(sub, case.return_value)?,
                        })
                    })
                    .collect::<TcResult<Vec<_>>>()?;
                Ok(self.builder().create_term(Term::TyFn(TyFn {
                    name: ty_fn.name,
                    general_params: subbed_general_params,
                    general_return_ty: subbed_general_return_ty,
                    cases: subbed_cases,
                })))
            }
            Term::TyFnTy(ty_fn_ty) => {
                // Apply the substitution to the parameters and return type.
                let subbed_params = self.apply_sub_to_params(sub, &ty_fn_ty.params)?;
                let subbed_return_ty = self.apply_sub_to_term(sub, ty_fn_ty.return_ty)?;
                Ok(self.builder().create_term(Term::TyFnTy(TyFnTy {
                    params: subbed_params,
                    return_ty: subbed_return_ty,
                })))
            }
            Term::AppTyFn(app_ty_fn) => {
                // Apply the substitution to the subject and arguments.
                let subbed_subject = self.apply_sub_to_term(sub, app_ty_fn.subject)?;
                let subbed_args = self.apply_sub_to_args(sub, &app_ty_fn.args)?;
                Ok(self.builder().create_term(Term::AppTyFn(AppTyFn {
                    subject: subbed_subject,
                    args: subbed_args,
                })))
            }
            Term::Unresolved(unresolved) => {
                // If the variable is in the substitution, substitute it, otherwise do nothing.
                match sub.get_sub_for(unresolved.into()) {
                    Some(subbed_term_id) => Ok(subbed_term_id),
                    None => Ok(term_id),
                }
            }
            // For the definite-level terms, recurse:
            Term::Level3(term) => {
                let subbed_term = self.apply_sub_to_level3_term(sub, term)?;
                Ok(self.builder().create_term(Term::Level3(subbed_term)))
            }
            Term::Level2(term) => {
                let subbed_term = self.apply_sub_to_level2_term(sub, term)?;
                Ok(self.builder().create_term(Term::Level2(subbed_term)))
            }
            Term::Level1(term) => {
                let subbed_term = self.apply_sub_to_level1_term(sub, term)?;
                Ok(self.builder().create_term(Term::Level1(subbed_term)))
            }
            Term::Level0(term) => {
                let subbed_term = self.apply_sub_to_level0_term(sub, term)?;
                Ok(self.builder().create_term(Term::Level0(subbed_term)))
            }
        }
    }
}
