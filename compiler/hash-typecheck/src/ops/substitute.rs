//! Functionality related to variable substitution inside terms/types.
use crate::{
    error::TcResult,
    storage::{
        primitives::{
            AppSub, AppTyFn, Arg, Args, FnTy, Level0Term, Level1Term, Level2Term, Level3Term,
            Param, ParamList, Params, Sub, Term, TermId, TupleTy, TyFn, TyFnCase, TyFnTy,
            UnresolvedTerm, Var,
        },
        AccessToStorage, AccessToStorageMut, StorageRefMut,
    },
};
use std::collections::HashMap;

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
    pub fn apply_sub_to_level3_term(&mut self, _: &Sub, term: Level3Term) -> TcResult<TermId> {
        match term {
            Level3Term::TrtKind => Ok(self
                .builder()
                .create_term(Term::Level3(Level3Term::TrtKind))),
        }
    }

    /// Apply the given substitution to the given [Level2Term], producing a new [Level2Term] with
    /// the substituted variables.
    pub fn apply_sub_to_level2_term(&mut self, sub: &Sub, term: Level2Term) -> TcResult<TermId> {
        match term {
            Level2Term::Trt(_) => {
                // Here we add the substitution to the term
                let builder = self.builder();
                Ok(builder
                    .create_app_sub_term(sub.clone(), builder.create_term(Term::Level2(term))))
            }
            Level2Term::AnyTy => Ok(self.builder().create_term(Term::Level2(Level2Term::AnyTy))),
        }
    }

    /// Apply the given substitution to the given [Level1Term], producing a new [Level1Term] with
    /// the substituted variables.
    pub fn apply_sub_to_level1_term(&mut self, sub: &Sub, term: Level1Term) -> TcResult<TermId> {
        match term {
            Level1Term::ModDef(_) => {
                // Here we add the substitution to the term
                let builder = self.builder();
                Ok(builder
                    .create_app_sub_term(sub.clone(), builder.create_term(Term::Level1(term))))
            }
            Level1Term::NominalDef(_) => {
                // Here we add the substitution to the term
                let builder = self.builder();
                Ok(builder
                    .create_app_sub_term(sub.clone(), builder.create_term(Term::Level1(term))))
            }
            Level1Term::Tuple(tuple_ty) => {
                // Apply to all members
                let subbed_members = self.apply_sub_to_params(sub, &tuple_ty.members)?;
                Ok(self
                    .builder()
                    .create_term(Term::Level1(Level1Term::Tuple(TupleTy {
                        members: subbed_members,
                    }))))
            }
            Level1Term::Fn(fn_ty) => {
                // Apply to parameters and return type
                let subbed_params = self.apply_sub_to_params(sub, &fn_ty.params)?;
                let subbed_return_ty = self.apply_sub_to_term(sub, fn_ty.return_ty)?;
                Ok(self
                    .builder()
                    .create_term(Term::Level1(Level1Term::Fn(FnTy {
                        params: subbed_params,
                        return_ty: subbed_return_ty,
                    }))))
            }
        }
    }

    /// Apply the given substitution to the given [Level0Term], producing a new [Level0Term] with
    /// the substituted variables.
    pub fn apply_sub_to_level0_term(&mut self, sub: &Sub, term: Level0Term) -> TcResult<TermId> {
        match term {
            Level0Term::Rt(ty_term_id) => {
                // Apply to the type of the runtime value
                let subbed_ty_term_id = self.apply_sub_to_term(sub, ty_term_id)?;
                Ok(self.builder().create_rt_term(subbed_ty_term_id))
            }
            Level0Term::EnumVariant(_) => {
                // Here we add the substitution to the term
                let builder = self.builder();
                Ok(builder
                    .create_app_sub_term(sub.clone(), builder.create_term(Term::Level0(term))))
            }
        }
    }

    /// Apply the given substitution to the term indexed by the given [TermId], producing a new
    /// term with the substituted variables.
    ///
    /// Sometimes, this will actually create a [Term::AppSub] somewhere inside the term tree, and
    /// those are the leaf nodes of the substitution application. This will happen with [ModDef],
    /// [TrtDef], [NominalDef], and [EnumVariant]. This is so that when [Access] is resolved for
    /// those types, the substitution is carried forward into the member term.
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
            Term::AppSub(app_sub) => {
                // Here, we have to substitute all X in * -> X pairs of the substitution, as well
                // as the subject term itself.
                let subbed_sub = app_sub
                    .sub
                    .pairs()
                    .map(|(from, to)| Ok((from, self.apply_sub_to_term(sub, to)?)))
                    .collect::<TcResult<HashMap<_, _>>>()?;
                let subbed_term = self.apply_sub_to_term(sub, app_sub.term)?;
                Ok(self.builder().create_term(Term::AppSub(AppSub {
                    sub: Sub::from_map(subbed_sub),
                    term: subbed_term,
                })))
            }
            // For the definite-level terms, recurse:
            Term::Level3(term) => self.apply_sub_to_level3_term(sub, term),
            Term::Level2(term) => self.apply_sub_to_level2_term(sub, term),
            Term::Level1(term) => self.apply_sub_to_level1_term(sub, term),
            Term::Level0(term) => self.apply_sub_to_level0_term(sub, term),
        }
    }
}
