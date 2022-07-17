//! Contains operations to get the type of a term.
use itertools::Itertools;

use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        macros::tc_panic,
    },
    storage::{
        primitives::{
            AccessOp, Arg, ArgsId, Level0Term, Level1Term, Level2Term, Level3Term, LitTerm,
            MemberData, ModDefOrigin, Param, ParamsId, Pattern, PatternId, PatternParamsId, Term,
            TermId,
        },
        AccessToStorage, AccessToStorageMut, StorageRefMut,
    },
};

use super::{unify::UnifyParamsWithArgsMode, AccessToOps, AccessToOpsMut};

/// Can resolve the type of a given term, as another term.
pub struct Typer<'gs, 'ls, 'cd, 's> {
    storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for Typer<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd, 's> AccessToStorageMut for Typer<'gs, 'ls, 'cd, 's> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

/// A version of [MemberData] where the type has been inferred if it was not
/// given in the member definition.
#[derive(Debug, Clone, Copy)]
pub struct InferredMemberData {
    pub ty: TermId,
    pub value: Option<TermId>,
}

impl<'gs, 'ls, 'cd, 's> Typer<'gs, 'ls, 'cd, 's> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    /// Get the type of the given term, as another term. This will copy over the
    /// location of the provided term to the new term within
    /// [LocationStore].
    ///
    /// First simplifies the term. If you already know you have a simplified
    /// term, you can use [Self::ty_of_simplified_term].
    pub(crate) fn infer_ty_of_term(&mut self, term_id: TermId) -> TcResult<TermId> {
        let simplified_term_id = self.simplifier().potentially_simplify_term(term_id)?;
        let new_term = self.infer_ty_of_simplified_term(simplified_term_id)?;

        Ok(new_term)
    }

    /// Infer the type of the given member, if it does not already exist.
    ///
    /// *Note*: Assumes the term is validated.
    pub(crate) fn infer_member_ty(
        &mut self,
        member_data: MemberData,
    ) -> TcResult<InferredMemberData> {
        match member_data {
            MemberData::Uninitialised { ty } => Ok(InferredMemberData { ty, value: None }),
            MemberData::InitialisedWithTy { ty, value } => {
                Ok(InferredMemberData { ty, value: Some(value) })
            }
            MemberData::InitialisedWithInferredTy { value } => {
                let ty = self.infer_ty_of_term(value)?;
                Ok(InferredMemberData { ty, value: Some(value) })
            }
        }
    }

    /// Get the type of the given term, given that it is simplified, as another
    /// term.
    ///
    /// **Warning**: This might produce unexpected behaviour if the term is not
    /// simplified.
    pub(crate) fn infer_ty_of_simplified_term(&mut self, term_id: TermId) -> TcResult<TermId> {
        let term = self.reader().get_term(term_id).clone();
        let new_term = match term {
            Term::Access(access_term) => {
                // Here we want to get the type of the subject, and ensure it contains this
                // property, and if so return it.
                let ty_id_of_subject = self.infer_ty_of_term(access_term.subject)?;
                match access_term.op {
                    // Only namespace is allowed by this point:
                    AccessOp::Namespace => {
                        let ty_access_term =
                            self.builder().create_ns_access(ty_id_of_subject, access_term.name);
                        self.simplifier().potentially_simplify_term(ty_access_term)
                    }
                    AccessOp::Property => {
                        tc_panic!(
                            term_id,
                            self,
                            "Property access should have already been simplified away!"
                        )
                    }
                }
            }
            Term::TyFnCall(app_ty_fn) => {
                // Here we want to get the type of the subject, and ensure it is a TyFnTy.
                // Then, we just apply the args to the type function:
                let ty_id_of_subject = self.infer_ty_of_term(app_ty_fn.subject)?;
                let reader = self.reader();
                let ty_of_subject = reader.get_term(ty_id_of_subject);
                match ty_of_subject {
                    Term::TyFnTy(ty_fn_ty) => {
                        let ty_fn_ty = ty_fn_ty.clone();
                        // Unify the type function type params with the given args:
                        let sub = self.unifier().unify_params_with_args(
                            ty_fn_ty.params,
                            app_ty_fn.args,
                            term_id,
                            ty_id_of_subject,
                            UnifyParamsWithArgsMode::SubstituteParamNamesForArgValues,
                        )?;
                        // Apply the substitution to the return type and use it as the result:
                        Ok(self.substituter().apply_sub_to_term(&sub, ty_fn_ty.return_ty))
                    }
                    _ => Err(TcError::UnsupportedTypeFunctionApplication {
                        subject_id: app_ty_fn.subject,
                    }),
                }
            }
            Term::TyFnTy(_) => {
                // The type of a type function type is Root
                Ok(self.builder().create_root_term())
            }
            Term::Var(var) => {
                // The type of a variable can be found by looking at the scopes to its
                // declaration:
                let var_member = self.scope_resolver().resolve_name_in_scopes(var.name, term_id)?;
                Ok(self.infer_member_ty(var_member.member.data)?.ty)
            }
            Term::TyFn(ty_fn) => {
                // The type of a type function is a type function type:
                Ok(self
                    .builder()
                    .create_ty_fn_ty_term(ty_fn.general_params, ty_fn.general_return_ty))
            }
            Term::Merge(terms) => {
                // The type of a merge is a merge of the inner terms:
                let tys_of_terms: Vec<_> = terms
                    .iter()
                    .map(|term| self.infer_ty_of_term(*term))
                    .collect::<TcResult<_>>()?;
                Ok(self.builder().create_merge_term(tys_of_terms))
            }
            Term::Union(_) => {
                // The type of a union is "RuntimeInstantiable":
                // @@Future: relax this
                let rt_instantiable_def = self.core_defs().runtime_instantiable_trt;
                Ok(self.builder().create_trt_term(rt_instantiable_def))
            }
            Term::AppSub(app_sub) => {
                // The type of an AppSub is the type of the subject, with the substitution
                // applied:
                let ty_of_subject = self.infer_ty_of_term(app_sub.term)?;
                Ok(self.substituter().apply_sub_to_term(&app_sub.sub, ty_of_subject))
            }
            Term::Unresolved(_) => {
                // The type of an unresolved variable X is typeof(X):
                Ok(self.builder().create_ty_of_term(term_id))
            }
            Term::Level3(level3_term) => match level3_term {
                Level3Term::TrtKind => {
                    // The type of TraitKind, is Root
                    Ok(self.builder().create_root_term())
                }
            },
            Term::Level2(level2_term) => match level2_term {
                // The type of any trait, or the "Type" trait, is just TraitKind:
                Level2Term::Trt(_) | Level2Term::AnyTy => Ok(self.builder().create_trt_kind_term()),
            },
            Term::Level1(level1_term) => match level1_term {
                Level1Term::ModDef(mod_def_id) => {
                    // The type of a mod def depends on its origin:
                    let reader = self.reader();
                    let mod_def = reader.get_mod_def(mod_def_id);
                    match mod_def.origin {
                        ModDefOrigin::TrtImpl(trt_impl) => {
                            // The type is the trait impl:
                            Ok(trt_impl)
                        }
                        ModDefOrigin::AnonImpl | ModDefOrigin::Mod | ModDefOrigin::Source(_) => {
                            // The rest is just "Type"
                            Ok(self.builder().create_any_ty_term())
                        }
                    }
                }
                Level1Term::NominalDef(_) | Level1Term::Tuple(_) | Level1Term::Fn(_) => {
                    // The type of any nominal def, function type, or tuple type, is
                    // "RuntimeInstantiable":
                    let rt_instantiable_def = self.core_defs().runtime_instantiable_trt;
                    Ok(self.builder().create_trt_term(rt_instantiable_def))
                }
            },
            Term::Level0(level0_term) => {
                match level0_term {
                    Level0Term::Rt(inner_ty) => {
                        // The type of a Rt(X) is X
                        Ok(inner_ty)
                    }
                    Level0Term::FnLit(fn_lit) => {
                        // Here we just return the function type element
                        Ok(fn_lit.fn_ty)
                    }
                    Level0Term::EnumVariant(enum_variant) => {
                        // The type of an enum variant is the enum
                        Ok(self.builder().create_nominal_def_term(enum_variant.enum_def_id))
                    }
                    Level0Term::FnCall(_) => {
                        tc_panic!(term_id, self, "Function call should have been simplified away when trying to get the type of the term!")
                    }
                    Level0Term::Tuple(tuple_lit) => {
                        // Get the type of the tuple arguments as parameters:
                        let params = self.infer_params_of_args(tuple_lit.members, false)?;
                        Ok(self.builder().create_tuple_ty_term(params))
                    }
                    Level0Term::Lit(lit_term) => {
                        // This gets the type of the literal

                        let var_to_resolve = match lit_term {
                            LitTerm::Str(_) => "str",
                            LitTerm::Int(_) => {
                                // @@Todo: do some more sophisticated inferring here
                                "i32"
                            }
                            LitTerm::Char(_) => "char",
                        };
                        let term = self.builder().create_var_term(var_to_resolve);
                        Ok(self.simplifier().potentially_simplify_term(term)?)
                    }
                }
            }
            Term::TyOf(_) => {
                // Since this is simplified already, all we can do is wrap it again..
                Ok(self.builder().create_ty_of_term(term_id))
            }
            // The type of root is typeof(root)
            Term::Root => {
                let builder = self.builder();
                Ok(builder.create_ty_of_term(builder.create_root_term()))
            }
        }?;

        self.location_store_mut().copy_location(term_id, new_term);
        Ok(new_term)
    }

    /// From the given [ArgsId], infer a [ParamsId] describing the the
    /// arguments.
    ///
    /// This will populate the default values with the values of the args if
    /// `populate_defaults` is true.
    pub(crate) fn infer_params_of_args(
        &mut self,
        args_id: ArgsId,
        populate_defaults: bool,
    ) -> TcResult<ParamsId> {
        let args = self.reader().get_args(args_id).clone();
        let origin = args.origin();
        let params_list: Vec<_> = args
            .into_positional()
            .into_iter()
            .map(|arg| {
                Ok(Param {
                    name: arg.name,
                    ty: self.infer_ty_of_term(arg.value)?,
                    default_value: if populate_defaults { Some(arg.value) } else { None },
                })
            })
            .collect::<TcResult<_>>()?;

        let params_id = self.builder().create_params(params_list.iter().copied(), origin);

        // Copy locations:
        for i in 0..params_list.len() {
            self.location_store_mut().copy_location((args_id, i), (params_id, i))
        }

        Ok(params_id)
    }

    /// From the given [PatternParamsId], infer a [ArgsId] describing the the
    /// arguments.
    pub(crate) fn infer_args_of_pattern_params(
        &mut self,
        pattern_params_id: PatternParamsId,
    ) -> TcResult<ArgsId> {
        let pattern_params = self.reader().get_pattern_params(pattern_params_id).clone();
        let origin = pattern_params.origin();
        let param_types: Vec<_> = pattern_params
            .into_positional()
            .into_iter()
            .map(|param| {
                Ok(Arg { name: param.name, value: self.get_term_of_pattern(param.pattern)? })
            })
            .collect::<TcResult<_>>()?;

        let args_id = self.builder().create_args(param_types.iter().copied(), origin);

        // Copy locations:
        for i in 0..param_types.len() {
            self.location_store_mut().copy_location((pattern_params_id, i), (args_id, i))
        }

        Ok(args_id)
    }

    /// Get the type of the given pattern, as a term.
    pub(crate) fn infer_ty_of_pattern(&mut self, pattern_id: PatternId) -> TcResult<TermId> {
        let pattern_term = self.get_term_of_pattern(pattern_id)?;
        self.infer_ty_of_term(pattern_term)
    }

    /// Get the term of the given pattern, whose type is the type of the pattern
    /// subject.
    pub(crate) fn get_term_of_pattern(&mut self, pattern_id: PatternId) -> TcResult<TermId> {
        let pattern = self.reader().get_pattern(pattern_id).clone();
        let ty_of_pattern = match pattern {
            Pattern::Mod(_) | Pattern::Ignore | Pattern::Binding(_) => {
                // We don't know this; it depends on the subject:
                Ok(self.builder().create_unresolved_term())
            }
            Pattern::Lit(lit_term) => {
                // The term of a literal pattern is the literal (lol):
                Ok(lit_term)
            }
            Pattern::Tuple(tuple_pattern) => {
                // For each parameter, get its type, and then create a tuple
                // type:
                let params_id = self.infer_args_of_pattern_params(tuple_pattern)?;
                let builder = self.builder();
                Ok(builder.create_tuple_lit_term(params_id))
            }
            Pattern::Constructor(constructor_pattern) => match constructor_pattern.params {
                Some(params) => {
                    // We have params to apply, so we need to create an FnCall
                    let args_id = self.infer_args_of_pattern_params(params)?;
                    let builder = self.builder();
                    Ok(builder.create_fn_call_term(constructor_pattern.subject, args_id))
                }
                None => {
                    // We just use the subject
                    Ok(constructor_pattern.subject)
                }
            },
            Pattern::Or(patterns) => {
                // Get the inner pattern types:
                let pattern_types: Vec<_> = patterns
                    .into_iter()
                    .map(|pattern| self.infer_ty_of_pattern(pattern))
                    .collect::<TcResult<_>>()?;
                // Create a union type:
                let builder = self.builder();
                Ok(builder.create_rt_term(builder.create_union_term(pattern_types)))
            }
            Pattern::If(pattern_if) => {
                // Forward to the pattern
                self.get_term_of_pattern(pattern_if.pattern)
            }
        }?;

        // Copy location:
        self.location_store_mut().copy_location(pattern_id, ty_of_pattern);

        Ok(ty_of_pattern)
    }

    /// Get the parameters of the given tuple term, if possible.
    ///
    /// This function returns Some(..) if the term is validated and simplified,
    /// and is a tuple term (either literal or Rt.). Otherwise it will
    /// return None.
    ///
    /// This function will populate default values if it can (if the tuple is a
    /// literal).
    pub(crate) fn get_params_ty_of_tuple_term(
        &mut self,
        tuple_term_id: TermId,
    ) -> TcResult<Option<ParamsId>> {
        let tuple_ty_id = self.infer_ty_of_simplified_term(tuple_term_id)?;

        // First, try to read the value as a tuple literal:
        let tuple_term = self.reader().get_term(tuple_term_id).clone();
        match tuple_term {
            Term::Level0(Level0Term::Tuple(tuple_lit)) => {
                Ok(Some(self.infer_params_of_args(tuple_lit.members, true)?))
            }
            _ => {
                // Otherwise, get the type and try to get the parameters that way:
                let tuple_ty = self.reader().get_term(tuple_ty_id).clone();
                match tuple_ty {
                    Term::Merge(terms) => {
                        // Try each term:
                        terms
                            .iter()
                            .copied()
                            .map(|term| self.get_params_ty_of_tuple_term(term))
                            .flatten_ok()
                            .next()
                            .transpose()
                    }
                    Term::Level1(Level1Term::Tuple(tuple_ty)) => Ok(Some(tuple_ty.members)),
                    _ => Ok(None),
                }
            }
        }
    }
}
