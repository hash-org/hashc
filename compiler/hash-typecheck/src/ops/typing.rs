//! Contains operations to get the type of a term.
use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{
            AccessOp, Level0Term, Level1Term, Level2Term, Level3Term, MemberData, ModDefOrigin,
            Term, TermId,
        },
        AccessToStorage, AccessToStorageMut, StorageRefMut,
    },
};

use super::{AccessToOps, AccessToOpsMut};

/// Can resolve the type of a given term, as another term.
pub struct Typer<'gs, 'ls, 'cd> {
    storage: StorageRefMut<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for Typer<'gs, 'ls, 'cd> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> AccessToStorageMut for Typer<'gs, 'ls, 'cd> {
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

impl<'gs, 'ls, 'cd> Typer<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    /// Get the type of the given term, as another term. This will copy over the
    /// location of the provided term to the new term within
    /// [LocationStore].
    ///
    /// First simplifies the term. If you already know you have a simplified
    /// term, you can use [Self::ty_of_simplified_term].
    pub(crate) fn ty_of_term(&mut self, term_id: TermId) -> TcResult<TermId> {
        let simplified_term_id = self.simplifier().potentially_simplify_term(term_id)?;
        let new_term = self.ty_of_simplified_term(simplified_term_id)?;

        self.location_store_mut().copy_location(term_id.into(), new_term.into());
        Ok(new_term)
    }

    /// Infer the type of the given member, if it does not already exist.
    ///
    /// *Note*: Assumes the term is validated.
    pub(crate) fn infer_member_data(
        &mut self,
        member_data: MemberData,
    ) -> TcResult<InferredMemberData> {
        match member_data {
            MemberData::Uninitialised { ty } => Ok(InferredMemberData { ty, value: None }),
            MemberData::InitialisedWithTy { ty, value } => {
                Ok(InferredMemberData { ty, value: Some(value) })
            }
            MemberData::InitialisedWithInferredTy { value } => {
                let ty = self.ty_of_term(value)?;
                Ok(InferredMemberData { ty, value: Some(value) })
            }
        }
    }

    /// Get the type of the given term, given that it is simplified, as another
    /// term.
    ///
    /// **Warning**: This might produce unexpected behaviour if the term is not
    /// simplified.
    pub(crate) fn ty_of_simplified_term(&mut self, term_id: TermId) -> TcResult<TermId> {
        let term = self.reader().get_term(term_id).clone();
        match term {
            Term::Access(access_term) => {
                // Here we want to get the type of the subject, and ensure it contains this
                // property, and if so return it.
                let ty_id_of_subject = self.ty_of_term(access_term.subject)?;
                match access_term.op {
                    // Only namespace is allowed by this point:
                    AccessOp::Namespace => {
                        let ty_access_term =
                            self.builder().create_ns_access(ty_id_of_subject, access_term.name);
                        self.simplifier().potentially_simplify_term(ty_access_term)
                    }
                    AccessOp::Property => {
                        panic!("Property access should have already been simplified away!")
                    }
                }
            }
            Term::AppTyFn(app_ty_fn) => {
                // Here we want to get the type of the subject, and ensure it is a TyFnTy.
                // Then, we just apply the args to the type function:
                let ty_id_of_subject = self.ty_of_term(app_ty_fn.subject)?;
                let reader = self.reader();
                let ty_of_subject = reader.get_term(ty_id_of_subject);
                match ty_of_subject {
                    Term::TyFnTy(ty_fn_ty) => {
                        let ty_fn_ty = ty_fn_ty.clone();
                        // Unify the type function type params with the given args:
                        let sub = self.unifier().unify_params_with_args(
                            ty_fn_ty.params,
                            app_ty_fn.args,
                            ty_id_of_subject,
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
                let var_member = self.scope_resolver().resolve_name_in_scopes(var.name)?;
                Ok(self.infer_member_data(var_member.data)?.ty)
            }
            Term::TyFn(ty_fn) => {
                // The type of a type function is a type function type:
                Ok(self
                    .builder()
                    .create_ty_fn_ty_term(ty_fn.general_params, ty_fn.general_return_ty))
            }
            Term::Merge(terms) => {
                // The type of a merge is a merge of the inner terms:
                let tys_of_terms: Vec<_> =
                    terms.iter().map(|term| self.ty_of_term(*term)).collect::<TcResult<_>>()?;
                Ok(self.builder().create_merge_term(tys_of_terms))
            }
            Term::AppSub(app_sub) => {
                // The type of an AppSub is the type of the subject, with the substitution
                // applied:
                let ty_of_subject = self.ty_of_term(app_sub.term)?;
                Ok(self.substituter().apply_sub_to_term(&app_sub.sub, ty_of_subject))
            }
            Term::Unresolved(_) => {
                // The type of an unresolved variable is unresolved:
                Ok(self.builder().create_unresolved_term())
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
                }
            }
            // The type of root is root
            Term::Root => Ok(self.builder().create_root_term()),
        }
    }
}
