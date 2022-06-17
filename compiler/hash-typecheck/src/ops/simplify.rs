//! Contains functionality to simplify terms into more concrete terms.

// @@Remove
#![allow(unused)]
use super::{
    params::pair_args_with_params, substitute::Substituter, unify::Unifier, AccessToOps,
    AccessToOpsMut,
};
use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{
            AccessOp, AccessTerm, AppTyFn, Level0Term, Level1Term, Level2Term, Level3Term, Member,
            NominalDef, ScopeId, StructFields, Term, TermId,
        },
        scope::ScopeStack,
        AccessToStorage, AccessToStorageMut, StorageRefMut,
    },
};
use hash_pipeline::traits::Tc;
use hash_source::identifier::Identifier;

/// Can perform simplification on terms.
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

    /// Resolve the given name in the scope with the given [ScopeId], originating from the given value.
    ///
    /// Returns the resolved member, or errors if no such member was found.
    fn resolve_name_member_in_scope(
        &self,
        name: Identifier,
        scope: ScopeId,
        value: TermId,
    ) -> TcResult<Member> {
        match self.reader().get_scope(scope).get(name) {
            Some(member) => Ok(member),
            None => {
                // Member not found!
                Err(TcError::UnresolvedNameInValue { name, value })
            }
        }
    }

    /// Resolve the given name in the scope with the given [ScopeId], originating from the given value.
    ///
    /// Returns [Some] if the member can be resolved with a value, [None] if it cannot because it
    /// has no value yet.
    fn resolve_name_in_scope(
        &self,
        name: Identifier,
        scope: ScopeId,
        value: TermId,
    ) -> TcResult<Option<TermId>> {
        match self.resolve_name_member_in_scope(name, scope, value)?.value {
            // Member found and has value, return it!
            Some(value) => Ok(Some(value)),
            // Cannot simplify yet, because the member does not have a defined value:
            None => Ok(None),
        }
    }

    /// Apply the given access term structure, if possible.
    fn apply_access_term(&mut self, access_term: &AccessTerm) -> TcResult<Option<TermId>> {
        let simplified_subject_id = self.potentially_simplify_term(access_term.subject_id)?;
        let simplified_subject = self.reader().get_term(simplified_subject_id).clone();

        // Helper for things that do not support accessing:
        let does_not_support_access = || -> TcResult<Option<TermId>> {
            Err(TcError::UnsupportedPropertyAccess {
                name: access_term.name,
                value: access_term.subject_id,
            })
        };

        // Helper for things that only support namespace access:
        let does_not_support_prop_access = || match access_term.op {
            AccessOp::Namespace => Ok(()),
            AccessOp::Property => Err(TcError::UnsupportedPropertyAccess {
                name: access_term.name,
                value: access_term.subject_id,
            }),
        };

        // Helper for things that only support property access:
        let does_not_support_ns_access = || match access_term.op {
            AccessOp::Namespace => Ok(()),
            AccessOp::Property => Err(TcError::UnsupportedNamespaceAccess {
                name: access_term.name,
                value: access_term.subject_id,
            }),
        };

        // Helper for name not found in value:
        let name_not_found = || {
            Err(TcError::UnresolvedNameInValue {
                name: access_term.name,
                value: simplified_subject_id,
            })
        };

        match simplified_subject {
            Term::Merge(terms) => {
                // Apply the access to each result. If there are multiple results, it means there
                // is an ambiguity which should be reported.
                let results: Vec<_> = terms
                    .iter()
                    .filter_map(|item| {
                        let item_access_term = AccessTerm {
                            subject_id: *item,
                            ..*access_term
                        };
                        self.apply_access_term(&item_access_term).transpose()
                    })
                    .collect::<TcResult<_>>()?;

                match results.as_slice() {
                    // Got no results, which means that the application did not result in any
                    // changed terms:
                    [] => Ok(None),
                    // We only got a single result, so we can use it:
                    [single_result] => Ok(Some(*single_result)),
                    // Got multiple results, which is ambiguous:
                    _ => Err(TcError::AmbiguousAccess {
                        access: access_term.clone(),
                    }),
                }
            }
            Term::AppSub(app_sub) => {
                // Apply the access on the subject:
                let inner_applied_term = self.apply_access_term(&AccessTerm {
                    subject_id: app_sub.term,
                    ..*access_term
                })?;
                match inner_applied_term {
                    Some(inner_applied_term) => {
                        // Successful access operation, apply the substitution on the result:
                        Ok(Some(
                            self.substituter()
                                .apply_sub_to_term(&app_sub.sub, inner_applied_term),
                        ))
                    }
                    None => Ok(None), // Access resulted in no change
                }
            }
            Term::Level3(_) => does_not_support_access(),
            Term::Level2(level2_term) => match level2_term {
                // Traits:
                Level2Term::Trt(trt_def_id) => {
                    does_not_support_prop_access()?;

                    // Resolve the member in the trait scope:
                    let trt_def_scope = self.reader().get_trt_def(trt_def_id).members;
                    self.resolve_name_in_scope(
                        access_term.name,
                        trt_def_scope,
                        access_term.subject_id,
                    )
                }
                // Cannot access members of the `Type` trait:
                Level2Term::AnyTy => does_not_support_access(),
            },
            Term::Level1(level1_term) => match level1_term {
                // Modules:
                Level1Term::ModDef(mod_def_id) => {
                    does_not_support_prop_access()?;

                    // Resolve the member in the module scope:
                    let mod_def_scope = self.reader().get_mod_def(mod_def_id).members;
                    self.resolve_name_in_scope(
                        access_term.name,
                        mod_def_scope,
                        access_term.subject_id,
                    )
                }
                // Nominals:
                Level1Term::NominalDef(nominal_def_id) => {
                    let reader = self.reader();
                    let nominal_def = reader.get_nominal_def(nominal_def_id);
                    match nominal_def {
                        NominalDef::Struct(struct_def) => {
                            // Struct type access results in the type of the term (given that it is
                            // a namespace operation)
                            does_not_support_prop_access()?;
                            match &struct_def.fields {
                                StructFields::Explicit(fields) => {
                                    match fields.get_by_name(access_term.name) {
                                        Some((_, field)) => {
                                            // Field found, now return its type as the result:
                                            Ok(Some(field.ty))
                                        }
                                        None => name_not_found(),
                                    }
                                }
                                // Opaque structs have no fields:
                                StructFields::Opaque => name_not_found(),
                            }
                        }
                        NominalDef::Enum(enum_def) => {
                            // Enum type access results in the runtime value of the variant
                            // (namespace operation).
                            does_not_support_prop_access()?;
                            match enum_def.variants.get(&access_term.name) {
                                Some(enum_variant) => {
                                    /// Return a term that refers to the variant (level 0)
                                    let name = enum_variant.name;
                                    Ok(Some(
                                        self.builder()
                                            .create_enum_variant_value_term(name, nominal_def_id),
                                    ))
                                }
                                None => name_not_found(),
                            }
                        }
                    }
                }
                // Tuples:
                Level1Term::Tuple(tuple_ty) => {
                    // Return the type of the member with the given name:
                    match tuple_ty.members.get_by_name(access_term.name) {
                        Some((_, member)) => Ok(Some(member.ty)),
                        None => name_not_found(),
                    }
                }
                Level1Term::Fn(_) => does_not_support_access(),
            },
            Term::Level0(level0_term) => match level0_term {
                // Runtime values:
                Level0Term::Rt(ty_term_id) => {
                    does_not_support_ns_access();
                    // If a property access is given, try to access `ty_term_id` with a namespace
                    // operator, and if that works (returning X) then it should resolve to Rt(X).
                    let ty_access_result = self.apply_access_term(&AccessTerm {
                        subject_id: ty_term_id,
                        name: access_term.name,
                        op: AccessOp::Namespace,
                    })?;
                    Ok(ty_access_result.map(|result| self.builder().create_rt_term(result)))
                }
                // Enum variants:
                Level0Term::EnumVariant(enum_variant) => {
                    does_not_support_ns_access();
                    // Try to resolve the field in the variant:
                    let reader = self.reader();
                    let nominal_def = reader.get_nominal_def(enum_variant.enum_def_id);
                    match nominal_def {
                        NominalDef::Enum(enum_def) => {
                            let fields = &enum_def
                                .variants
                                .get(&enum_variant.variant_name)
                                .expect("Enum variant name not found in def!")
                                .fields;
                            match fields.get_by_name(access_term.name) {
                                Some((_, field)) => {
                                    // Field found, now return a Rt(X) of the field type X as the result.
                                    let field_ty = field.ty;
                                    Ok(Some(self.builder().create_rt_term(field_ty)))
                                }
                                None => name_not_found(),
                            }
                        }
                        NominalDef::Struct(_) => unreachable!("Got struct def ID in enum variant!"),
                    }
                }
            },
            Term::Access(_) => todo!(),
            Term::Var(_) => todo!(),
            Term::TyFn(_) => todo!(),
            Term::TyFnTy(_) => todo!(),
            Term::AppTyFn(_) => todo!(),
            Term::Unresolved(_) => todo!(),
        }
    }

    /// Apply the given type function application structure, if possible.
    fn apply_ty_fn(&mut self, apply_ty_fn: &AppTyFn) -> TcResult<Option<TermId>> {
        let simplified_subject_id = self.potentially_simplify_term(apply_ty_fn.subject)?;
        let simplified_subject = self.reader().get_term(simplified_subject_id).clone();
        match simplified_subject {
            Term::TyFn(ty_fn) => {
                // Keep track of encountered errors so that if no cases match, we can return all of
                // them.
                let mut errors = vec![];
                let mut results = vec![];

                // First, ensure they unify with general params:
                let _ = self
                    .unifier()
                    .unify_params_with_args(&ty_fn.general_params, &apply_ty_fn.args)?;

                // Try to match each of the cases:
                for case in &ty_fn.cases {
                    match self
                        .unifier()
                        .unify_params_with_args(&case.params, &apply_ty_fn.args)
                    {
                        Ok(sub) => {
                            // Successful, add the return value to result, subbed with the
                            // substitution, and continue:
                            results.push(
                                self.substituter()
                                    .apply_sub_to_term(&sub, case.return_value),
                            );
                        }
                        Err(err) => {
                            // Unsuccessful, push the error to the errors and continue:
                            errors.push(err);
                        }
                    }
                }

                if results.is_empty() {
                    // If we have no results, we have to return an error:
                    Err(TcError::InvalidTypeFunctionApplication {
                        type_fn: simplified_subject_id,
                        args: apply_ty_fn.args.clone(),
                        unification_errors: errors,
                    })
                } else {
                    // Otherwise, merge the results
                    Ok(Some(self.builder().create_term(Term::Merge(results))))
                }
            }
            Term::Access(_) => todo!(),
            Term::Var(_) => todo!(),
            Term::Merge(_) => todo!(),
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

    /// Simplify the given term, just returning the original if no simplification occurred.
    pub fn potentially_simplify_term(&mut self, term_id: TermId) -> TcResult<TermId> {
        Ok(self.simplify_term(term_id)?.unwrap_or(term_id))
    }

    /// Simplify the given term, if possible.
    pub fn simplify_term(&mut self, term_id: TermId) -> TcResult<Option<TermId>> {
        let value = self.reader().get_term(term_id).clone();
        match value {
            Term::Merge(inner) => {
                // @@Enhancement: here we can also collapse degenerate elements

                // Simplify each element of the merge:
                let inner = inner;
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
            Term::AppSub(apply_sub) => Ok(Some(
                // @@Performance: add Option<_> to the substituter to return
                // terms which don't have the variables in them.
                self.substituter()
                    .apply_sub_to_term(&apply_sub.sub, apply_sub.term),
            )),
            Term::AppTyFn(apply_ty_fn) => self.apply_ty_fn(&apply_ty_fn),
            Term::Access(access_term) => self.apply_access_term(&access_term),
            // Cannot simplify:
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
