//! Contains functionality to simplify terms into more concrete terms.
use std::iter;

use hash_ast::ast::ParamOrigin;
use hash_source::identifier::Identifier;
use hash_types::{
    arguments::ArgsId,
    params::ParamsId,
    terms::{TermId, TermListId},
    AccessOp, AccessTerm, Arg, ConstructedTerm, Field, FnLit, FnTy, Level0Term, Level1Term,
    Level2Term, Level3Term, Member, Mutability, NominalDef, Param, ScopeKind, StructFields, Term,
    TupleLit, TupleTy, TyFn, TyFnCall, TyFnCase, TyFnTy,
};
use hash_utils::store::{SequenceStore, SequenceStoreKey, Store};
use itertools::Itertools;

use super::{substitute::Substituter, unify::Unifier, AccessToOps};
use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        macros::{tc_panic, tc_panic_on_many},
    },
    storage::{AccessToStorage, StorageRef},
};

/// Can perform simplification on terms.
pub struct Simplifier<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for Simplifier<'tc> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

// Helper for [Simplifier::apply_access_term] erroring for things that do not
// support accessing:
fn does_not_support_access<T>(access_term: &AccessTerm) -> TcResult<T> {
    Err(TcError::UnsupportedPropertyAccess { name: access_term.name, value: access_term.subject })
}

// Helper for [Simplifier::apply_access_term] erroring for things that only
// support namespace access:
fn does_not_support_prop_access(access_term: &AccessTerm) -> TcResult<Identifier> {
    match access_term.op {
        AccessOp::Namespace => match access_term.name {
            Field::Named(name) => Ok(name),
            _ => Err(TcError::UnsupportedPropertyAccess {
                name: access_term.name,
                value: access_term.subject,
            }),
        },
        AccessOp::Property => Err(TcError::UnsupportedPropertyAccess {
            name: access_term.name,
            value: access_term.subject,
        }),
    }
}

// Helper for [Simplifier::apply_access_term] erroring for things that only
// support property access:
fn does_not_support_ns_access(access_term: &AccessTerm) -> TcResult<()> {
    match access_term.op {
        AccessOp::Property => Ok(()),
        AccessOp::Namespace => Err(TcError::UnsupportedNamespaceAccess {
            name: access_term.name,
            value: access_term.subject,
        }),
    }
}

// Helper for [Simplifier::apply_access_term] erroring for name not found in
// value:
fn name_not_found<T>(access_term: &AccessTerm) -> TcResult<T> {
    Err(TcError::UnresolvedNameInValue {
        name: access_term.name,
        value: access_term.subject,
        op: access_term.op,
    })
}

// Helper for converting a [TcError::UnresolvedVariable] into a
// [TcError::UnresolvedNameInValue] if originating from the given access term.
fn turn_unresolved_var_err_into_unresolved_in_value_err(
    access_term: &AccessTerm,
) -> impl Fn(TcError) -> TcError + '_ {
    |err| {
        match err {
        TcError::UnresolvedVariable { name, value: _ } if let Field::Named(field_name) = access_term.name && name == field_name => {
            TcError::UnresolvedNameInValue {
                name: access_term.name,
                value: access_term.subject,
                op: access_term.op,
            }
        }
        _ => err,
    }
    }
}

impl<'tc> Simplifier<'tc> {
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Convenience method to get a [Unifier].
    fn unifier(&self) -> Unifier {
        Unifier::new(self.storages())
    }

    /// Convenience method to get a [Substituter].
    fn substituter(&self) -> Substituter {
        Substituter::new(self.storages())
    }

    /// Convert an accessed type (or any other type for that matter) along with
    /// a subject type, into a method call term.
    ///
    /// This is done by first ensuring that the accessed type is a function
    /// type. Then the first argument of the function type (self) is unified
    /// with the subject type. If that succeeds, a method function type is
    /// created, which is the same as the resolved function type without the
    /// first parameter (with the substitution from the unification applied).
    fn turn_accessed_ty_and_subject_ty_into_method(
        &self,
        accessed_ty: TermId,
        subject_ty: TermId,
        initial_subject_term: TermId,
        initial_property_name: Field,
    ) -> TcResult<TermId> {
        // Invalid because it is not a method:
        let invalid_property_access = || {
            Err(TcError::InvalidPropertyAccessOfNonMethod {
                subject: initial_subject_term,
                property: initial_property_name,
            })
        };

        // Here we need to ensure the result is a function type, and if so call
        // it with the self parameter:
        //
        // @@Todo: infer type variables here:
        match self.validator().term_is_fn_ty(accessed_ty)? {
            Some(fn_ty) => {
                let params = self.params_store().get_owned_param_list(fn_ty.params);

                if params.positional().is_empty() {
                    invalid_property_access()?;
                }

                // Unify the first parameter type with the subject:
                let sub = self.unifier().unify_terms(subject_ty, params.positional()[0].ty)?;

                // Apply the substitution on the parameters and return type:
                let subbed_params_id = self.substituter().apply_sub_to_params(&sub, fn_ty.params);
                let _subbed_return_ty = self.substituter().apply_sub_to_term(&sub, fn_ty.return_ty);

                let builder = self.builder();

                // Return the substituted type without the first parameter:
                Ok(builder.create_rt_term(builder.create_fn_ty_term(
                    builder.create_params(
                        self.params_store().map_fast(subbed_params_id, |params| {
                            params.iter().skip(1).copied().collect_vec()
                        }),
                        ParamOrigin::Fn,
                    ),
                    fn_ty.return_ty,
                )))
            }
            _ => {
                // Invalid because it is not a method:
                invalid_property_access()
            }
        }
    }

    /// Try to access the given `field_name` as a field on the given term, which
    /// is the inner type of a runtime term. Returns `Some(X)` if found,
    /// where X is the runtime term of the result, or `None` if not found.
    fn access_struct_or_tuple_field(
        &self,
        rt_term_ty_id: TermId,
        property: Field,
    ) -> TcResult<Option<TermId>> {
        // Invalid because it is not a method:
        let invalid_property_access =
            || Err(TcError::InvalidPropertyAccessOfNonMethod { subject: rt_term_ty_id, property });

        match self.reader().get_term(rt_term_ty_id) {
            Term::SetBound(set_bound) => {
                // Enter the bound and try access
                let result = self.scope_manager().enter_scope(set_bound.scope, |this| {
                    this.simplifier().access_struct_or_tuple_field(set_bound.term, property)
                })?;
                match result {
                    Some(result) => Ok(Some(
                        self.discoverer()
                            .potentially_apply_set_bound_to_term(set_bound.scope, result)?,
                    )),
                    None => Ok(None),
                }
            }
            Term::Merge(terms) => {
                // Try this for each term:
                for idx in terms.to_index_range() {
                    let term = self.term_list_store().get_at_index(terms, idx);

                    match self.access_struct_or_tuple_field(term, property)? {
                        Some(result) => return Ok(Some(result)),
                        None => continue,
                    }
                }
                Ok(None)
            }
            Term::Level1(level1_term) => {
                // If it is a struct or a tuple, and the name is resolved in the fields, return
                // the (runtime) value of the field.
                if let Level1Term::NominalDef(nominal_def_id) = level1_term {
                    let nominal_def = self.reader().get_nominal_def(nominal_def_id);

                    if let NominalDef::Struct(struct_def) = nominal_def {
                        if let StructFields::Explicit(fields) = &struct_def.fields {
                            let reader = self.reader();
                            let fields = reader.get_params_owned(*fields);

                            match property {
                                Field::Named(name) => {
                                    if let Some((_, param)) = fields.get_by_name(name) {
                                        let param_ty = param.ty;
                                        return Ok(Some(self.builder().create_rt_term(param_ty)));
                                    }
                                }
                                Field::Numeric(_) => return invalid_property_access(),
                            }
                        }
                    }
                } else if let Level1Term::Tuple(TupleTy { members }) = level1_term {
                    match property {
                        Field::Named(name) => {
                            if let Some((_, param)) = self.params_store().get_by_name(members, name)
                            {
                                return Ok(Some(self.builder().create_rt_term(param.ty)));
                            }
                        }
                        Field::Numeric(index) => {
                            if index < members.len() {
                                let member = self.params_store().get_at_index(members, index);
                                return Ok(Some(member.ty));
                            }
                        }
                    }
                }
                // Otherwise return none.
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    /// Apply the given access, comprising of a name and an operator, to the
    /// given [Level0Term], if possible, originating from the given
    /// [AccessTerm].
    fn apply_access_to_level0_term(
        &self,
        term: &Level0Term,
        access_term: &AccessTerm,
        originating_term: TermId,
    ) -> TcResult<Option<TermId>> {
        match term {
            // Runtime values:
            Level0Term::Rt(ty_term_id) => {
                does_not_support_ns_access(access_term)?;

                // First, check if the value is a struct instance, in which case we are
                // accessing one of its members:
                if let Some(access_result) =
                    self.access_struct_or_tuple_field(*ty_term_id, access_term.name)?
                {
                    return Ok(Some(access_result));
                }

                // If a property access is given, first try to access `ty_term_id` with a
                // namespace operator, to resolve "method calls":
                let ty_access_result = self.apply_access_term(&AccessTerm {
                    subject: *ty_term_id,
                    name: access_term.name,
                    op: AccessOp::Namespace,
                });
                if let Ok(Some(ty_access_result)) = ty_access_result {
                    // To get the function type, we need to get the type of the result.
                    let ty_of_ty_access_result = self.typer().infer_ty_of_term(ty_access_result)?;
                    // Then we can try turn this into a method call
                    return Some(self.turn_accessed_ty_and_subject_ty_into_method(
                        ty_of_ty_access_result,
                        *ty_term_id,
                        access_term.subject,
                        access_term.name,
                    ))
                    .transpose();
                }

                // Instead of giving up here, we can instead try to access the property
                // of the type of the ty_access_result, and then see if the result is
                // level 1. If it is, we can perform the same transformation as above.
                //
                // This is possible because traits will return the type of their
                // members when accessing members.
                let ty_of_ty_term_id = self.typer().infer_ty_of_term(*ty_term_id)?;
                let accessed_result = self.apply_access_term(&AccessTerm {
                    subject: ty_of_ty_term_id,
                    name: access_term.name,
                    op: AccessOp::Namespace,
                })?;

                match accessed_result {
                    Some(accessed_result) => {
                        // Now we can try turn this into a method call
                        Some(self.turn_accessed_ty_and_subject_ty_into_method(
                            accessed_result,
                            *ty_term_id,
                            access_term.subject,
                            access_term.name,
                        ))
                        .transpose()
                    }
                    // If none of this worked, then the property wasn't found:
                    None => name_not_found(access_term),
                }
            }
            // Enum variants do not support access (only through pattern matching):
            Level0Term::EnumVariant(_) => does_not_support_access(access_term),
            Level0Term::FnLit(_) => does_not_support_access(access_term),
            Level0Term::FnCall(_) => {
                tc_panic!(
                    originating_term,
                    self,
                    "Function call in access apply should have already been simplified!"
                )
            }
            Level0Term::Constructed(ConstructedTerm { members, .. })
            | Level0Term::Tuple(TupleLit { members }) => match access_term.name {
                Field::Named(name) => {
                    if let Some((_, member)) = self.args_store().get_by_name(*members, name) {
                        Ok(Some(member.value))
                    } else {
                        name_not_found(access_term)
                    }
                }
                Field::Numeric(index) => {
                    if index < members.len() {
                        let member = self.args_store().get_at_index(*members, index);
                        Ok(Some(member.value))
                    } else {
                        name_not_found(access_term)
                    }
                }
            },
            Level0Term::Unit(_) | Level0Term::Lit(_) => {
                // Create an Rt(..) of the value wrapped, and use that as the subject.
                let term_value = Level0Term::Rt(self.typer().infer_ty_of_term(originating_term)?);
                let term = self.builder().create_term(Term::Level0(term_value.clone()));
                self.location_store().copy_location(originating_term, term);
                self.apply_access_to_level0_term(&term_value, access_term, term)
            }
        }
    }

    /// Apply the given access, comprising of a name and an operator, to the
    /// given [Level1Term], if possible, originating from the given
    /// [AccessTerm].
    fn apply_access_to_level1_term(
        &self,
        term: &Level1Term,
        access_term: &AccessTerm,
    ) -> TcResult<Option<TermId>> {
        match term {
            // Modules:
            Level1Term::ModDef(mod_def_id) => {
                let name = does_not_support_prop_access(access_term)?;

                // Get the scope of the module.
                let mod_def_scope = self.reader().get_mod_def(*mod_def_id).members;
                self.scope_manager().enter_scope(mod_def_scope, |this| {
                    // Resolve the name:
                    let name_var = this.builder().create_var_term(name);
                    let result = this.simplifier().simplify_term(name_var).map_err(
                        turn_unresolved_var_err_into_unresolved_in_value_err(access_term),
                    )?;

                    if let Some(member) =
                        this.scope_store().map_fast(mod_def_scope, |scope| scope.get(name))
                    {
                        if let Some(inner_term) = result {
                            this.location_store()
                                .copy_location((mod_def_scope, member.1), inner_term)
                        }
                    }
                    Ok(result)
                })
            }
            // Nominals:
            Level1Term::NominalDef(nominal_def_id) => {
                match self.reader().get_nominal_def(*nominal_def_id) {
                    NominalDef::Struct(_) => {
                        // Struct type access is not valid.
                        does_not_support_access(access_term)
                    }
                    NominalDef::Enum(enum_def) => {
                        // Enum type access results in the runtime value of the variant
                        // (namespace operation).
                        let name = does_not_support_prop_access(access_term)?;

                        match enum_def.variants.get(&name) {
                            Some(enum_variant) => {
                                // Return a term that refers to the variant (level 0)
                                let name = enum_variant.name;
                                Ok(Some(
                                    self.builder()
                                        .create_enum_variant_value_term(name, *nominal_def_id),
                                ))
                            }
                            None => name_not_found(access_term),
                        }
                    }
                    NominalDef::Unit(_) => does_not_support_access(access_term),
                }
            }
            Level1Term::Tuple(_tuple_ty) => does_not_support_access(access_term),
            Level1Term::Fn(_) => does_not_support_access(access_term),
        }
    }

    /// Apply the given access, comprising of a name and an operator, to the
    /// given [Level2Term], if possible, originating from the given
    /// [AccessTerm].
    fn apply_access_to_level2_term(
        &self,
        term: &Level2Term,
        access_term: &AccessTerm,
    ) -> TcResult<Option<TermId>> {
        match term {
            // Traits:
            Level2Term::Trt(trt_def_id) => {
                let name = does_not_support_prop_access(access_term)?;

                // Get the scope of the trait.
                let trt_def_scope = self.reader().get_trt_def(*trt_def_id).members;
                let result = self.scope_manager().enter_scope(trt_def_scope, |this| {
                    // Resolve the type of the name:
                    let name_var = this.builder().create_var_term(name);
                    this.typer()
                        .infer_ty_of_term(name_var)
                        .map_err(turn_unresolved_var_err_into_unresolved_in_value_err(access_term))
                })?;

                Ok(Some(result))
            }
            Level2Term::SizedTy | Level2Term::AnyTy => does_not_support_access(access_term),
        }
    }

    /// Apply the given access, comprising of a name and an operator, to the
    /// given [Level3Term], if possible, originating from the given
    /// [AccessTerm].
    fn apply_access_to_level3_term(
        &self,
        _term: &Level3Term,
        access_term: &AccessTerm,
    ) -> TcResult<Option<TermId>> {
        does_not_support_access(access_term)
    }

    /// Apply the given access term structure, if possible.
    fn apply_access_term(&self, access_term: &AccessTerm) -> TcResult<Option<TermId>> {
        let simplified_subject_id = self.potentially_simplify_term(access_term.subject)?;
        let simplified_subject = self.reader().get_term(simplified_subject_id);

        // Overwrite the the `subject` with `simplified_subject_id`
        let access_term = &AccessTerm { subject: simplified_subject_id, ..*access_term };

        match simplified_subject {
            Term::Union(terms) => {
                // Here we try to access the nominal with the given name:
                self.term_list_store().map_fast(terms, |terms| {
                    if let Field::Named(name) = access_term.name {
                        for term in terms {
                            if self.oracle().term_is_named(*term, name) {
                                return Ok(Some(*term));
                            }
                        }
                    }
                    Err(TcError::UnresolvedNameInValue {
                        name: access_term.name,
                        op: access_term.op,
                        value: simplified_subject_id,
                    })
                })
            }
            Term::Merge(terms) => {
                // Apply the access to each result. If there are multiple results, it means
                // there is an ambiguity which should be reported.
                let results: Vec<_> = self
                    .reader()
                    .get_term_list_owned(terms)
                    .iter()
                    .filter_map(|item| {
                        let item_access_term = AccessTerm { subject: *item, ..*access_term };
                        self.apply_access_term(&item_access_term).ok().flatten()
                    })
                    .collect();

                match results.as_slice() {
                    // Got no results, which means that the application did not result in any
                    // changed terms:
                    [] => Ok(None),
                    // We only got a single result, so we can use it:
                    [single_result] => Ok(Some(*single_result)),
                    // Got multiple results, which is ambiguous:
                    results => Err(TcError::AmbiguousAccess {
                        access: *access_term,
                        results: results.to_vec(),
                    }),
                }
            }
            Term::SetBound(set_bound) => {
                let result = self.scope_manager().enter_scope(set_bound.scope, |this| {
                    this.simplifier()
                        .apply_access_term(&AccessTerm { subject: set_bound.term, ..*access_term })
                })?;
                match result {
                    Some(result) => Ok(Some(
                        self.discoverer()
                            .potentially_apply_set_bound_to_term(set_bound.scope, result)?,
                    )),
                    None => Ok(None),
                }
            }
            Term::Level3(level3_term) => {
                self.apply_access_to_level3_term(&level3_term, access_term)
            }
            Term::Level2(level2_term) => {
                self.apply_access_to_level2_term(&level2_term, access_term)
            }
            Term::Level1(level1_term) => {
                self.apply_access_to_level1_term(&level1_term, access_term)
            }
            Term::Level0(level0_term) => {
                self.apply_access_to_level0_term(&level0_term, access_term, simplified_subject_id)
            }
            // @@Todo: infer type vars:
            Term::TyFn(_) => does_not_support_access(access_term),
            Term::TyFnTy(_) => does_not_support_access(access_term),
            Term::Root => does_not_support_access(access_term),
            Term::TyOf(_) => does_not_support_access(access_term),
            // @@Enhancement: maybe we can allow this and add it to some hints context of the
            // variable.
            Term::Unresolved(_) => does_not_support_access(access_term),
            Term::BoundVar(_)
            | Term::ScopeVar(_)
            | Term::Access(_)
            | Term::Var(_)
            | Term::TyFnCall(_) => {
                // We cannot perform any accessing here:
                Ok(None)
            }
        }
    }

    /// Apply the given type function application structure, if possible.
    fn apply_ty_fn(&self, apply_ty_fn: &TyFnCall) -> TcResult<Option<TermId>> {
        let potentially_simplified_subject = self.simplify_term(apply_ty_fn.subject)?;

        let (subject_simplified, simplified_subject_id) = (
            potentially_simplified_subject.is_some(),
            potentially_simplified_subject.unwrap_or(apply_ty_fn.subject),
        );
        let simplified_subject = self.reader().get_term(simplified_subject_id);

        // Helper for errors:
        let cannot_apply = || -> TcResult<Option<TermId>> {
            Err(TcError::UnsupportedTyFnApplication { subject_id: simplified_subject_id })
        };

        match simplified_subject {
            Term::TyFn(ty_fn) => {
                // Keep track of encountered errors so that if no cases match, we can return all
                // of them.
                let mut errors = vec![];
                let mut results = vec![];

                // First, ensure they unify with general params:
                //
                // @@Correctness: do we need to apply this sub anywhere?
                let _ = self.unifier().unify_params_with_args(
                    ty_fn.general_params,
                    apply_ty_fn.args,
                    apply_ty_fn.subject,
                    simplified_subject_id,
                )?;

                // Try to match each of the cases:
                for case in &ty_fn.cases {
                    match self.unifier().unify_params_with_args(
                        case.params,
                        apply_ty_fn.args,
                        apply_ty_fn.subject,
                        simplified_subject_id,
                    ) {
                        Ok(_) => {
                            // Successful: create a set bound scope and wrap the return value in it:
                            let scope = self.scope_manager().make_set_bound_scope(
                                case.params,
                                apply_ty_fn.args,
                                apply_ty_fn.subject,
                                simplified_subject_id,
                            );
                            let result = self
                                .discoverer()
                                .potentially_apply_set_bound_to_term(scope, case.return_value)?;
                            results.push(result);
                        }
                        Err(err) => {
                            // Unsuccessful, push the error to the errors and continue:
                            errors.push(err);
                        }
                    }
                }

                if results.is_empty() {
                    // If we have no results, we have to return an error:
                    Err(TcError::InvalidTyFnApplication {
                        type_fn: simplified_subject_id,
                        cases: ty_fn.cases,
                        args: apply_ty_fn.args,
                        unification_errors: errors,
                    })
                } else {
                    // Otherwise, merge the results
                    Ok(Some(self.builder().create_merge_term(results.into_iter())))
                }
            }
            Term::Unresolved(_) => {
                // We don't know the type of this, so we refuse it.
                // @@Enhancement: here we can unify the unresolved term with a type function
                // term ?
                cannot_apply()
            }
            Term::Merge(_) => {
                // Cannot apply a merge:
                // @@Enhancement: this could be allowed in the future.
                cannot_apply()
            }
            Term::SetBound(_)
            | Term::Union(_)
            | Term::Root
            | Term::TyFnTy(_)
            | Term::Level3(_)
            | Term::Level2(_)
            | Term::Level1(_)
            | Term::Level0(_)
            | Term::ScopeVar(_)
            | Term::BoundVar(_)
            | Term::TyOf(_) => {
                // Cannot apply if it didn't simplify to a type function:
                cannot_apply()
            }
            Term::Access(_) | Term::Var(_) | Term::TyFnCall(_) => {
                let simplified_args = self.simplifier().simplify_args(apply_ty_fn.args)?;

                // Return a simplified term if either the subject or the args were simplified.
                if let Some(args) = simplified_args {
                    Ok(Some(self.builder().create_app_ty_fn_term(simplified_subject_id, args)))
                } else if subject_simplified {
                    Ok(Some(
                        self.builder()
                            .create_app_ty_fn_term(simplified_subject_id, apply_ty_fn.args),
                    ))
                } else {
                    // We cannot perform any more simplification:
                    Ok(None)
                }
            }
        }
    }

    /// Check whether a given term can be used as a `Constructed` subject. There
    /// are three cases that need to be considered within this check:
    ///
    /// - If the given term is a nominal struct definition
    /// - If merge, then only one member should be a struct
    /// - If app-sub, child can be struct/merge (recurse) * apply sub before
    ///   return *
    ///
    /// *Note*: Expects the term to be simplified.
    pub fn is_term_constructable(&self, term_id: TermId) -> bool {
        match self.reader().get_term(term_id) {
            Term::Merge(terms) => self
                .reader()
                .get_term_list_owned(terms)
                .iter()
                .any(|term| self.is_term_constructable(*term)),
            Term::SetBound(set_bound) => self.is_term_constructable(set_bound.term),
            Term::Level1(Level1Term::NominalDef(_)) => true,
            _ => false,
        }
    }

    /// Use a given term can as the `Constructed` subject. There
    /// are three cases that a term can be used as the subject of a
    /// [ConstructedTerm].
    ///
    /// - If the given term is a nominal struct definition
    /// - If merge, then only one member should be a struct
    /// - If app-sub, child can be struct/merge (recurse) * apply sub before
    ///   return *
    ///
    /// *Note*: Expects the term to be simplified.

    pub fn use_term_as_constructed_subject(
        &self,
        term_id: TermId,
        args: ArgsId,
        args_subject: TermId,
    ) -> TcResult<ConstructedTerm> {
        let reader = self.reader();
        let term = reader.get_term(term_id);

        let cannot_use_as_call_subject = || Err(TcError::InvalidCallSubject { term: term_id });

        match term {
            Term::Merge(terms) => {
                // Recurse into the inner terms:
                let terms = terms;
                let results: Vec<_> = self
                    .reader()
                    .get_term_list_owned(terms)
                    .iter()
                    .filter_map(|item| {
                        self.use_term_as_constructed_subject(*item, args, args_subject).ok()
                    })
                    .collect();

                match results.as_slice() {
                    // Got no results, cannot be used as fn call:
                    [] => cannot_use_as_call_subject(),
                    // We only got a single result, so we can use it:
                    [result] => {
                        // The result we got, we have to merge its return value with the rest of
                        // the elements:
                        Ok(ConstructedTerm { members: result.members, subject: term_id })
                    }
                    // Got multiple results, which should not happen:
                    results => {
                        let result_terms = results
                            .iter()
                            .map(|result| {
                                self.builder()
                                    .create_term(Term::Level0(Level0Term::Constructed(*result)))
                            })
                            .collect::<Vec<_>>();

                        tc_panic_on_many!(
                                result_terms,
                                self,
                                "Got multiple results when using merge term as constructed subject: {:?}",
                                results
                            )
                    }
                }
            }
            Term::SetBound(set_bound) => {
                let constructed_result =
                    self.scope_manager().enter_scope(set_bound.scope, |this| {
                        this.simplifier().use_term_as_constructed_subject(
                            set_bound.term,
                            args,
                            term_id,
                        )
                    })?;
                // Add back the set bound in the subject
                Ok(ConstructedTerm {
                    members: self
                        .discoverer()
                        .apply_set_bound_to_args(set_bound.scope, constructed_result.members)?,
                    subject: self.discoverer().potentially_apply_set_bound_to_term(
                        set_bound.scope,
                        constructed_result.subject,
                    )?,
                })
            }
            Term::Level1(Level1Term::NominalDef(nominal_def_id)) => {
                let reader = self.reader();

                let nominal_def = reader.get_nominal_def(nominal_def_id);
                match nominal_def {
                    NominalDef::Struct(struct_def) => {
                        let params_id = match struct_def.fields {
                            StructFields::Explicit(params) => params,
                            StructFields::Opaque => {
                                // Cannot construct an opaque struct:
                                return cannot_use_as_call_subject();
                            }
                        };

                        // Perform inference by using the resolved parameters and then
                        // applying them to the supplied arguments. This will fill
                        // in any missing default arguments, and then apply an appropriate
                        // unification between the arguments and parameters.
                        let members = self.typer().infer_args_from_params(
                            args,
                            params_id,
                            term_id,
                            args_subject,
                        )?;

                        Ok(ConstructedTerm { subject: term_id, members })
                    }
                    NominalDef::Unit(_) => cannot_use_as_call_subject(),
                    // @@Remove
                    NominalDef::Enum(_) => cannot_use_as_call_subject(),
                }
            }
            _ => cannot_use_as_call_subject(),
        }
    }

    /// Use the given term in function call subject position, returning the type
    /// of the function it represents.
    ///
    /// The following terms can be used as this:
    /// - Function literals (`FnLit(..)`)
    /// - Runtime values of function type (`Rt(FnTy(..))`)
    /// - Enum variants with members (`EnumVariant(..)`)
    /// - Struct definitions (`NominalDef(StructDef(..))`)
    ///
    /// *Note*: Expects the term to be simplified.
    pub fn use_term_as_fn_call_subject(&self, term_id: TermId) -> TcResult<FnTy> {
        let reader = self.reader();
        let term = reader.get_term(term_id);

        let cannot_use_as_fn_call_subject = || Err(TcError::InvalidCallSubject { term: term_id });

        match term {
            Term::Merge(terms) => {
                // Recurse into the inner terms:
                let terms = terms;
                let results: Vec<_> = self
                    .reader()
                    .get_term_list_owned(terms)
                    .iter()
                    .enumerate()
                    .filter_map(|(i, item)| {
                        Some((i, self.use_term_as_fn_call_subject(*item).ok()?))
                    })
                    .collect();

                match results.as_slice() {
                    // Got no results, cannot be used as fn call:
                    [] => cannot_use_as_fn_call_subject(),
                    // We only got a single result, so we can use it:
                    [(result_i, single_result)] => {
                        // The result we got, we have to merge its return value with the rest of
                        // the elements:
                        let params = single_result.params;
                        let return_ty = self.builder().create_merge_term(
                            iter::once(single_result.return_ty).chain(
                                self.reader()
                                    .get_term_list_owned(terms)
                                    .iter()
                                    .enumerate()
                                    .filter(|(i, _)| i != result_i)
                                    .map(|(_, term)| *term),
                            ),
                        );
                        Ok(FnTy { params, return_ty })
                    }
                    // Got multiple results, which should not happen:
                    results => {
                        let result_terms = results
                            .iter()
                            .map(|(_, result)| {
                                self.builder().create_term(Term::Level1(Level1Term::Fn(*result)))
                            })
                            .collect::<Vec<_>>();
                        tc_panic_on_many!(
                            result_terms,
                            self,
                            "Got multiple results when using merge term as fn call subject: {:?}",
                            results
                        )
                    }
                }
            }
            Term::SetBound(set_bound) => {
                let result = self.scope_manager().enter_scope(set_bound.scope, |this| {
                    this.simplifier().use_term_as_fn_call_subject(set_bound.term)
                })?;
                Ok(FnTy {
                    params: self
                        .discoverer()
                        .apply_set_bound_to_params(set_bound.scope, result.params)?,
                    return_ty: self
                        .discoverer()
                        .potentially_apply_set_bound_to_term(set_bound.scope, result.return_ty)?,
                })
            }
            Term::Unresolved(_) => {
                // @@Future: Here maybe create a function type with unknown args and return?
                // For now error:
                cannot_use_as_fn_call_subject()
            }
            Term::Level0(level0_term) => {
                // Ensure it is either an enum variant, or Rt(Fn(..)) or
                // FnLit(..)
                let reader = self.reader();
                match level0_term {
                    Level0Term::Rt(rt_inner_term_id) => {
                        // Only accept if it is a function type inside:
                        match reader.get_term(rt_inner_term_id) {
                            Term::Level1(Level1Term::Fn(fn_ty)) => Ok(fn_ty),
                            _ => cannot_use_as_fn_call_subject(),
                        }
                    }
                    Level0Term::FnLit(fn_lit) => {
                        // Just return the inner type:
                        match reader.get_term(fn_lit.fn_ty) {
                            Term::Level1(Level1Term::Fn(fn_ty)) => Ok(fn_ty),
                            _ => tc_panic!(
                                fn_lit.fn_ty,
                                self,
                                "Unexpected non-function type as fn_ty field of FnLit"
                            ),
                        }
                    }
                    Level0Term::EnumVariant(enum_variant) => {
                        // Only accept if it is an enum variant with data:

                        // @@PartiallyBroken: Merged impls on the enum would not carry
                        // forward here, we need to somehow carry them forward while doing
                        // the access.
                        let variant = self.oracle().get_enum_variant_info(enum_variant);
                        let enum_ty =
                            self.builder().create_nominal_def_term(enum_variant.enum_def_id);
                        match variant.fields {
                            Some(fields) => Ok(FnTy { params: fields, return_ty: enum_ty }),
                            None => cannot_use_as_fn_call_subject(),
                        }
                    }
                    Level0Term::FnCall(_) => {
                        tc_panic!(term_id, self, "Function call should have already been simplified away when resolving function call subject")
                    }
                    Level0Term::Lit(_) => cannot_use_as_fn_call_subject(),
                    Level0Term::Tuple(_) => cannot_use_as_fn_call_subject(),
                    Level0Term::Constructed(_) => cannot_use_as_fn_call_subject(),
                    Level0Term::Unit(_) => cannot_use_as_fn_call_subject(),
                }
            }

            // Cannot be used as function call subjects:
            // (Remember, the term should have already been simplified)
            Term::Level2(_)
            | Term::Level1(_)
            | Term::Level3(_)
            | Term::TyFnCall(_)
            | Term::TyFn(_)
            | Term::TyFnTy(_)
            | Term::Root
            | Term::Var(_)
            | Term::Union(_)
            | Term::ScopeVar(_)
            | Term::BoundVar(_)
            | Term::TyOf(_)
            | Term::Access(_) => cannot_use_as_fn_call_subject(),
        }
    }

    /// Simplify the given term, just returning the original if no
    /// simplification occurred.
    #[inline]
    pub(crate) fn potentially_simplify_term(&self, term_id: TermId) -> TcResult<TermId> {
        Ok(self.simplify_term(term_id)?.unwrap_or(term_id))
    }

    /// Simplify the given [Level0Term], if possible.
    pub(crate) fn simplify_level0_term(
        &self,
        term: &Level0Term,
        originating_term: TermId,
    ) -> TcResult<Option<TermId>> {
        match term {
            // For Rt(..), try to simplify the inner term:
            Level0Term::Rt(inner) => {
                Ok(self.simplify_term(*inner)?.map(|result| self.builder().create_rt_term(result)))
            }
            Level0Term::FnLit(fn_lit) => {
                // For FnLit(..), simplify the inner function type:
                let simplified_fn_ty = self.simplify_term(fn_lit.fn_ty)?;

                // We don't need to simplify the return value because it will not ever be used
                // for unification.

                match simplified_fn_ty {
                    None => Ok(None),
                    Some(simplified_fn_ty) => {
                        Ok(Some(self.builder().create_term(Term::Level0(Level0Term::FnLit(
                            FnLit { fn_ty: simplified_fn_ty, return_value: fn_lit.return_value },
                        )))))
                    }
                }
            }
            Level0Term::EnumVariant(_) => Ok(None),
            Level0Term::FnCall(call) if self.is_term_constructable(call.subject) => {
                let simplified_subject = self.potentially_simplify_term(call.subject)?;
                let constructed_ty = self.use_term_as_constructed_subject(
                    simplified_subject,
                    call.args,
                    originating_term,
                )?;

                let term = self
                    .builder()
                    .create_term(Term::Level0(Level0Term::Constructed(constructed_ty)));

                Ok(Some(term))
            }
            Level0Term::FnCall(call) => {
                // Apply the function:

                // Must be a function:
                let simplified_subject = self.potentially_simplify_term(call.subject)?;
                let fn_ty = self.use_term_as_fn_call_subject(simplified_subject)?;

                // Unify params with args:
                let params_sub = self.unifier().unify_params_with_args(
                    fn_ty.params,
                    call.args,
                    simplified_subject,
                    originating_term,
                )?;

                // Apply the substitution to the return value:
                let subbed_return_value =
                    self.substituter().apply_sub_to_term(&params_sub, fn_ty.return_ty);

                Ok(Some(self.builder().create_rt_term(subbed_return_value)))
            }
            Level0Term::Tuple(TupleLit { members }) => {
                // Simplify inner terms:
                let simplified_members = self.simplify_args(*members)?;
                match simplified_members {
                    Some(members) => Ok(Some(self.builder().create_tuple_lit_term(members))),
                    None => Ok(None),
                }
            }
            Level0Term::Lit(_) => Ok(None),
            Level0Term::Constructed(ConstructedTerm { subject, members }) => {
                let simplified_subject = self.simplify_term(*subject)?;
                let simplified_members = self.simplify_args(*members)?;

                if simplified_subject.is_some() || simplified_members.is_some() {
                    let subject = simplified_subject.unwrap_or(*subject);
                    let members = simplified_members.unwrap_or(*members);

                    Ok(Some(self.builder().create_constructed_term(subject, members)))
                } else {
                    Ok(None)
                }
            }
            Level0Term::Unit(_) => Ok(None),
        }
    }

    /// Simplify the given [Level1Term], if possible.
    pub(crate) fn simplify_level1_term(&self, term: &Level1Term) -> TcResult<Option<TermId>> {
        match term {
            Level1Term::ModDef(_) | Level1Term::NominalDef(_) => Ok(None),
            Level1Term::Tuple(tuple_ty) => {
                // Simplify each inner type
                let simplified_members = self.simplify_params(tuple_ty.members)?;

                Ok(simplified_members.map(|simplified_members| {
                    self.builder().create_term(Term::Level1(Level1Term::Tuple(TupleTy {
                        members: simplified_members,
                    })))
                }))
            }
            Level1Term::Fn(fn_ty) => {
                // Simplify params and return type, and if either was simplified, return a new
                // simplified type.
                let simplified_params = self.simplify_params(fn_ty.params)?;
                let simplified_return_ty = self.simplify_term(fn_ty.return_ty)?;
                match (&simplified_params, simplified_return_ty) {
                    (None, None) => Ok(None),
                    _ => Ok(Some(self.builder().create_term(Term::Level1(Level1Term::Fn(FnTy {
                        params: simplified_params.unwrap_or(fn_ty.params),
                        return_ty: simplified_return_ty.unwrap_or(fn_ty.return_ty),
                    }))))),
                }
            }
        }
    }

    /// Simplify the given [Level2Term], if possible.
    pub(crate) fn simplify_level2_term(&self, term: &Level2Term) -> TcResult<Option<TermId>> {
        match term {
            Level2Term::Trt(_) | Level2Term::AnyTy | Level2Term::SizedTy => Ok(None),
        }
    }

    /// Simplify the given [Level3Term], if possible.
    pub(crate) fn simplify_level3_term(&self, term: &Level3Term) -> TcResult<Option<TermId>> {
        match term {
            Level3Term::TrtKind => Ok(None),
        }
    }

    /// Simplify the given [ArgsId], if possible.
    pub(crate) fn simplify_args(&self, args_id: ArgsId) -> TcResult<Option<ArgsId>> {
        let args = self.args_store().get_owned_param_list(args_id);

        // Simplify values:
        let mut simplified_once = false;
        let result = args
            .positional()
            .iter()
            .map(|arg| {
                Ok(Arg {
                    name: arg.name,
                    value: self
                        .simplify_term(arg.value)?
                        .map(|result| {
                            simplified_once = true;
                            result
                        })
                        .unwrap_or(arg.value),
                })
            })
            .collect::<TcResult<Vec<_>>>()?;

        // Only return the new args if we simplified them:
        if simplified_once {
            let new_args =
                self.builder().create_args(result, self.args_store().get_origin(args_id));
            self.location_store().copy_locations(args_id, new_args);

            Ok(Some(new_args))
        } else {
            Ok(None)
        }
    }

    /// Simplify the given [ParamsId], if possible.
    pub(crate) fn simplify_params(&self, params_id: ParamsId) -> TcResult<Option<ParamsId>> {
        let params = self.params_store().get_owned_param_list(params_id);

        // Simplify types and default values:
        let mut simplified_once = false;
        let result = params
            .positional()
            .iter()
            .map(|param| {
                Ok(Param {
                    name: param.name,
                    // Type:
                    ty: self
                        .simplify_term(param.ty)?
                        .map(|result| {
                            simplified_once = true;
                            result
                        })
                        .unwrap_or(param.ty),
                    // Default value:
                    default_value: param
                        .default_value
                        .map(|default_value| {
                            Ok(self
                                .simplify_term(default_value)?
                                .map(|result| {
                                    simplified_once = true;
                                    result
                                })
                                .unwrap_or(default_value))
                        })
                        .transpose()?,
                })
            })
            .collect::<TcResult<Vec<_>>>()?;

        // Only return the new params if we simplified them:
        if simplified_once {
            let new_params =
                self.builder().create_params(result, self.params_store().get_origin(params_id));
            self.location_store().copy_locations(params_id, new_params);

            Ok(Some(new_params))
        } else {
            Ok(None)
        }
    }

    /// Simplify the given set of terms by performing the following operations
    /// (where ^ is the separator of the list):
    ///
    /// - Applying idempotency: B ^ B ^ C becomes B ^ C
    /// - Flattening nests: B ^ (C ^ D) becomes B ^ C ^ D
    /// - Simplifying inner terms:
    ///  (<T> => (str, T))<i32> ^ C becomes (str, i32) ^ C
    /// - Distributivity: @@Todo, @@Enhancement
    ///
    /// This is to be used for merge and union types.
    pub fn simplify_algebraic_term_list(
        &self,
        terms: TermListId,
        is_nested: impl Fn(&Term) -> Option<TermListId>,
    ) -> TcResult<Option<TermListId>> {
        let mut simplified_once = false;

        // Flatten nests (associativity);
        // Also simplify inner terms
        let flattened: Vec<TermId> = self
            .reader()
            .get_term_list_owned(terms)
            .into_iter()
            .map(|term_id| {
                // Check if the term is a nested list, and if so flatten it:
                let simplified_term_id = self
                    .simplifier()
                    .simplify_term(term_id)?
                    .map(|x| {
                        simplified_once = true;
                        x
                    })
                    .unwrap_or(term_id);

                let term = self.reader().get_term(simplified_term_id);

                match is_nested(&term) {
                    // It is a merge, flatten it (this also means the merge has been
                    // simplified):
                    Some(terms) => {
                        simplified_once = true;
                        Ok(self.reader().get_term_list_owned(terms))
                    }
                    // Not a merge, just return a single-element vector:
                    _ => Ok(vec![simplified_term_id]),
                }
            })
            .flatten_ok()
            .collect::<TcResult<_>>()?;

        // Merge equal terms (idempotency)
        let mut merged: Vec<_> = flattened.iter().copied().map(Some).collect();
        for terms in flattened.iter().enumerate().combinations(2) {
            match terms.as_slice() {
                [(first_idx, &first), (second_idx, &second)] => {
                    // Try to merge the two terms if they are the same:
                    if self.unifier().terms_are_equal(first, second) {
                        simplified_once = true;
                        merged[*first_idx] = merged[*first_idx].map(|_| first);
                        merged[*second_idx] = None;
                    } else {
                        merged[*first_idx] = merged[*first_idx].map(|_| first);
                        merged[*second_idx] = merged[*second_idx].map(|_| second);
                    }
                }
                _ => unreachable!(),
            }
        }

        let result = self.term_list_store().create_from_iter_fast(merged.into_iter().flatten());

        // Only return if it has been simplified
        if !simplified_once {
            Ok(None)
        } else {
            Ok(Some(result))
        }
    }

    /// Simplify the given term, if possible.
    ///
    /// This does not perform all validity checks, some are performed by
    /// [super::Typer], and all are by [super::Validator].
    pub(crate) fn simplify_term(&self, term_id: TermId) -> TcResult<Option<TermId>> {
        // Check if we have already performed a simplification on this term, if so
        // return the result.
        if let Some(term) = self.cacher().has_been_simplified(term_id) {
            return Ok(Some(term));
        }

        let value = self.reader().get_term(term_id);
        let new_term = match value {
            Term::Merge(inner) => Ok(self
                .simplify_algebraic_term_list(inner, |term| match term {
                    Term::Merge(terms) => Some(*terms),
                    _ => None,
                })?
                .map(|result| self.builder().create_term(Term::Merge(result)))),
            Term::Union(inner) => Ok(self
                .simplify_algebraic_term_list(inner, |term| match term {
                    Term::Union(terms) => Some(*terms),
                    _ => None,
                })?
                .map(|result| self.builder().create_term(Term::Union(result)))),
            Term::SetBound(set_bound) => {
                let simplified_inner =
                    self.scope_manager().enter_scope(set_bound.scope, |this| {
                        this.simplifier().simplify_term(set_bound.term)
                    })?;
                match simplified_inner {
                    Some(simplified) => Ok(Some(
                        self.discoverer()
                            .potentially_apply_set_bound_to_term(set_bound.scope, simplified)?,
                    )),
                    None => Ok(self
                        .discoverer()
                        .apply_set_bound_to_term(set_bound.scope, set_bound.term)?),
                }
            }
            Term::TyFnCall(apply_ty_fn) => {
                let applied = self.apply_ty_fn(&apply_ty_fn)?;
                Ok(applied)
            }
            Term::Access(access_term) => self.apply_access_term(&access_term),
            // Turn the variable into a ScopeVar:
            Term::Var(var) => {
                // First resolve the name:
                let scope_member =
                    self.scope_manager().resolve_name_in_scopes(var.name, term_id)?;
                let scope_kind =
                    self.scope_store().map_fast(scope_member.scope_id, |scope| scope.kind);
                match scope_kind {
                    ScopeKind::Bound => {
                        // Create a bound var if it is part of a bound:
                        let bound_var = self.builder().create_bound_var_term(var.name);
                        self.location_store().copy_location(term_id, bound_var);
                        Ok(Some(self.potentially_simplify_term(bound_var)?))
                    }
                    _ => {
                        // Create a scope var otherwise:
                        let scope_var = self.builder().create_scope_var_term(
                            var.name,
                            scope_member.scope_id,
                            scope_member.index,
                        );
                        self.location_store().copy_location(term_id, scope_var);
                        Ok(Some(self.potentially_simplify_term(scope_var)?))
                    }
                }
            }
            // Resolve the variable to its value if it is set and closed.
            Term::ScopeVar(var) => {
                let scope_member = self.scope_manager().get_scope_var_member(var);
                match scope_member.member {
                    Member::Bound(_) => Ok(None),
                    Member::Constant(constant) => constant
                        .if_closed(|value| Some(self.potentially_simplify_term(value)))
                        .transpose(),
                    Member::SetBound(set_bound) => {
                        Ok(Some(self.potentially_simplify_term(set_bound.value)?))
                    }
                    // @@Correctness: is this always valid? What's the difference between constant
                    // and runtime immutable?
                    Member::Variable(variable) if variable.mutability == Mutability::Immutable => {
                        Ok(Some(self.potentially_simplify_term(variable.value)?))
                    }
                    Member::Variable(_variable) => Ok(None),
                }
            }
            // Nothing can be done for bound vars
            Term::BoundVar(_) => Ok(None),
            Term::TyFn(ty_fn) => {
                // Simplify each constituent of the type function, and if any are successfully
                // simplified, the whole thing can be simplified:

                // Simplify general params and return
                let simplified_general_params = self.simplify_params(ty_fn.general_params)?;

                let param_scope = self.scope_manager().make_bound_scope(ty_fn.general_params);
                let simplified_general_return_ty =
                    self.scope_manager().enter_scope(param_scope, |this| {
                        this.simplifier().simplify_term(ty_fn.general_return_ty)
                    })?;

                // Simplify each of the cases
                let simplified_cases: Vec<_> = ty_fn
                    .cases
                    .iter()
                    .map(|case| {
                        let simplified_params = self.simplify_params(case.params)?;

                        let param_scope = self.scope_manager().make_bound_scope(case.params);
                        let (simplified_return_ty, simplified_return_value) =
                            self.scope_manager().enter_scope(param_scope, |this| {
                                let simplified_return_ty =
                                    this.simplifier().simplify_term(case.return_ty)?;
                                let simplified_return_value =
                                    this.simplifier().simplify_term(case.return_value)?;
                                Ok((simplified_return_ty, simplified_return_value))
                            })?;

                        // A case is simplified if any of its constituents is simplified:
                        match (&simplified_params, simplified_return_ty, simplified_return_value) {
                            (None, None, None) => Ok(None),
                            _ => Ok(Some(TyFnCase {
                                params: simplified_params.unwrap_or(case.params),
                                return_ty: simplified_return_ty.unwrap_or(case.return_ty),
                                return_value: simplified_return_value.unwrap_or(case.return_value),
                            })),
                        }
                    })
                    .collect::<TcResult<_>>()?;

                // A type function is simplified if any of its constituents is simplified:
                match (&simplified_general_params, simplified_general_return_ty) {
                    // No simplification occurred:
                    (None, None) if simplified_cases.iter().all(|x| x.is_none()) => Ok(None),
                    // Otherwise, build the simplified type function:
                    _ => Ok(Some(
                        self.builder().create_term(Term::TyFn(TyFn {
                            name: ty_fn.name,
                            general_params: simplified_general_params
                                .unwrap_or(ty_fn.general_params),
                            general_return_ty: simplified_general_return_ty
                                .unwrap_or(ty_fn.general_return_ty),
                            cases: simplified_cases
                                .into_iter()
                                .zip(ty_fn.cases.into_iter())
                                .map(|(simplified_case, old_case)| {
                                    simplified_case.unwrap_or(old_case)
                                })
                                .collect(),
                        })),
                    )),
                }
            }
            Term::TyFnTy(ty_fn_ty) => {
                // Simplify params and return, and if either is simplified, the whole term is
                // simplified.
                let simplified_params = self.simplify_params(ty_fn_ty.params)?;

                let param_scope = self.scope_manager().make_bound_scope(ty_fn_ty.params);
                let simplified_return_ty =
                    self.scope_manager().enter_scope(param_scope, |this| {
                        this.simplifier().simplify_term(ty_fn_ty.return_ty)
                    })?;

                match (&simplified_params, simplified_return_ty) {
                    (None, None) => Ok(None),
                    _ => Ok(Some(self.builder().create_term(Term::TyFnTy(TyFnTy {
                        params: simplified_params.unwrap_or(ty_fn_ty.params),
                        return_ty: simplified_return_ty.unwrap_or(ty_fn_ty.return_ty),
                    })))),
                }
            }
            Term::TyOf(term) => {
                // Get the type of the term:
                Ok(Some(self.typer().infer_ty_of_term(term)?))
            }
            Term::Unresolved(_) => {
                // Cannot do anything here:
                Ok(None)
            }
            // Recurse for definite-level terms:
            Term::Level3(term) => self.simplify_level3_term(&term),
            Term::Level2(term) => self.simplify_level2_term(&term),
            Term::Level1(term) => self.simplify_level1_term(&term),
            Term::Level0(term) => self.simplify_level0_term(&term, term_id),
            // Root cannot be simplified:
            Term::Root => Ok(None),
        }?;

        // Copy over the location if a new term was created
        if let Some(new_term) = new_term {
            self.location_store().copy_location(term_id, new_term);

            // We want to add an entry for the operation within the cache...
            self.cacher().add_simplification_entry(term_id, new_term);
        }

        Ok(new_term)
    }
}
