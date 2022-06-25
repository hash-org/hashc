//! Contains utilities to validate terms.
use super::{AccessToOps, AccessToOpsMut};
use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{
            Args, FnTy, Level0Term, Level1Term, Level2Term, MemberData, ModDefId, ModDefOrigin,
            Mutability, NominalDefId, Params, Scope, ScopeId, ScopeKind, Sub, Term, TermId,
            TrtDefId,
        },
        AccessToStorage, AccessToStorageMut, StorageRefMut,
    },
};

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

/// Used to communicate the result of a successful term validation, which
/// produces the simplified term as well as its type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TermValidation {
    pub simplified_term_id: TermId,
    pub term_ty_id: TermId,
}

/// Helper type for [Validator::validate_merge_element], to keep track of the
/// kind of the merge (whether it is level 2, level 1, or not known yet).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MergeKind {
    Unknown,
    Level2,
    Level1 { nominal_attached: Option<TermId> },
}

/// Helper type for [Validator::validate_constant_scope], to determine in what
/// capacity the `Self` member should be existing in the scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(unused)] // @@Todo: remove
enum SelfMode {
    NotAllowed,
    Allowed,
    Required,
}

impl<'gs, 'ls, 'cd> Validator<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    /// Validate the members of the given constant scope.
    ///
    /// Allows uninitialised members in the scope if `allow_uninitialised` is
    /// true.
    fn validate_constant_scope(
        &mut self,
        scope_id: ScopeId,
        allow_uninitialised: bool,
        _self_mode: SelfMode,
    ) -> TcResult<()> {
        // @@Design: when do we insert each member into the scope? As we go or all at
        // once? For now, we insert as we go.

        // Enter the progressive scope:
        let progressive_scope = Scope::new(ScopeKind::Constant, []);
        let progressive_scope_id = self.scope_store_mut().create(progressive_scope);
        self.scopes_mut().append(progressive_scope_id);

        // @@Performance: sad that we have to clone here:
        let scope = self.reader().get_scope(scope_id).clone();
        for member in scope.iter() {
            // This should have been checked in semantic analysis:
            assert!(
                member.mutability == Mutability::Mutable,
                "Found mutable member in constant scope!"
            );

            // Add the member to the progressive scope so that this and next members can
            // access it.
            self.scope_store_mut().get_mut(progressive_scope_id).add(member);

            // Validate the member:
            match member.data {
                MemberData::Uninitialised { ty } if !allow_uninitialised => {
                    return Err(TcError::UninitialisedMemberNotAllowed { member_ty: ty });
                }
                MemberData::Uninitialised { ty } => {
                    // Validate only the type
                    self.validate_term(ty)?;
                }
                MemberData::InitialisedWithTy { ty, value } => {
                    // Validate the term, the type, and unify them.
                    let TermValidation { term_ty_id, .. } = self.validate_term(value)?;
                    let TermValidation { simplified_term_id: simplified_ty_id, .. } =
                        self.validate_term(ty)?;
                    let _ = self.unifier().unify_terms(term_ty_id, simplified_ty_id)?;
                }
                MemberData::InitialisedWithInferredTy { value } => {
                    // Validate the term, and the type
                    let TermValidation { term_ty_id, .. } = self.validate_term(value)?;
                    // @@PotentiallyRedundant: is this necessary? shouldn't this be an invariant
                    // already?
                    self.validate_term(term_ty_id)?;
                }
            }

            // @@Incomplete: here we also need to ensure that the member does
            // not directly access itself (i.e. `a := a`).
        }

        // Leave the progressive scope:
        let popped_scope = self.scopes_mut().pop_scope();
        assert!(popped_scope == progressive_scope_id);

        Ok(())
    }

    /// Ensure that the given `scope` implements the trait at the given
    /// `trt_def_term_id`, after applying the given substitution to the
    /// trait.
    ///
    /// This also validates that `trt_def_term_id` is a (validated) trait
    /// definition.
    ///
    /// Assumes that `scope` has already been validated.
    fn ensure_scope_implements_trait(
        &mut self,
        trt_def_term_id: TermId,
        trt_sub: &Sub,
        scope_originating_term_id: TermId,
        scope_id: ScopeId,
    ) -> TcResult<()> {
        let scope = self.reader().get_scope(scope_id).clone();

        // Simplify the term and ensure it is a trait
        let simplified_trt_def_term_id =
            self.simplifier().potentially_simplify_term(trt_def_term_id)?;
        let reader = self.reader();
        let simplified_trt_def_term = reader.get_term(simplified_trt_def_term_id);

        // Ensure the term leads to a trait definition:
        match simplified_trt_def_term {
            Term::AppSub(app_sub) => {
                let app_sub = app_sub.clone();
                // Recurse to inner term
                let unified_sub = self.unifier().unify_subs(&trt_sub, &app_sub.sub)?;
                self.ensure_scope_implements_trait(
                    app_sub.term,
                    &unified_sub,
                    scope_originating_term_id,
                    scope_id,
                )
            }
            Term::Level2(Level2Term::Trt(trt_def_id)) => {
                let trt_def_id = *trt_def_id;
                let trt_def_members = self.reader().get_trt_def(trt_def_id).members;
                // @@Performance: cloning :((
                let trt_def_members = self.reader().get_scope(trt_def_members).clone();

                // Ensure all members have been implemented:
                for trt_member in trt_def_members.iter() {
                    let trt_member_data = self.typer().infer_member_data(trt_member.data)?;

                    if let Some(scope_member) = scope.get(trt_member.name) {
                        // Infer the type of the scope member:
                        let scope_member_data =
                            self.typer().infer_member_data(scope_member.data)?;

                        // Apply the substitution to the trait member first:
                        let trt_member_ty_subbed =
                            self.substituter().apply_sub_to_term(&trt_sub, trt_member_data.ty);

                        // Unify the types of the scope member and the substituted trait member:
                        let _ =
                            self.unifier().unify_terms(scope_member_data.ty, trt_member_ty_subbed);
                    } else {
                        return Err(TcError::TraitImplementationMissingMember {
                            trt_def_term_id,
                            trt_impl_term_id: scope_originating_term_id,
                            trt_def_missing_member_term_id: trt_member_data.ty,
                        });
                    }
                }

                // @@Design: do we want to block the implementation of members
                // that are not in the trait definition?
                Ok(())
            }
            _ => Err(TcError::CannotImplementNonTrait {
                supposed_trait_term: simplified_trt_def_term_id,
            }),
        }
    }

    /// Validate the module definition of the given [ModDefId], defined in
    /// `originating_term_id`.
    pub fn validate_mod_def(
        &mut self,
        mod_def_id: ModDefId,
        originating_term_id: TermId,
    ) -> TcResult<()> {
        let reader = self.reader();
        let mod_def = reader.get_mod_def(mod_def_id);
        let mod_def_members = mod_def.members;
        let mod_def_origin = mod_def.origin;

        // Validate all members:
        // Bound vars should already be in scope.
        self.validate_constant_scope(mod_def_members, false, SelfMode::Allowed)?;

        // Ensure if it is a trait impl it implements all the trait members.
        if let ModDefOrigin::TrtImpl(trt_def_term_id) = mod_def_origin {
            self.ensure_scope_implements_trait(
                trt_def_term_id,
                &Sub::empty(),
                originating_term_id,
                mod_def_members,
            )?;
        }

        Ok(())
    }

    /// Validate the trait definition of the given [TrtDefId]
    pub fn validate_trt_def(&mut self, _trt_def_id: TrtDefId) -> TcResult<()> {
        // Ensure Self exists?
        // @@Design: do we allow traits without self?
        todo!()
    }

    /// Validate the nominal definition of the given [NominalDefId]
    pub fn validate_nominal_def(&mut self, _nominal_def_id: NominalDefId) -> TcResult<()> {
        // Ensure all members have level 1 types/level 0 default values and the default
        // values are of the given type.
        todo!()
    }

    /// Ensure the element `merge_element_term_id` of the merge with the given
    /// `merge_term_id` is either level 2 (along with the merge being all
    /// level 2), or level 1 (along with the merge being all level 1).
    /// Furthermore, if it is level 1, the merge should only have zero or one
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
            Err(TcError::InvalidElementOfMerge { term: merge_element_term_id })
        };

        // Helper to ensure that a merge is level 2, returns the updated MergeKind.
        let ensure_merge_is_level2 = || -> TcResult<MergeKind> {
            match *merge_kind {
                MergeKind::Unknown => {
                    // Now we know that the merge should be level 2
                    Ok(MergeKind::Level2)
                }
                MergeKind::Level2 => {
                    // Merge is already level 2, all good:
                    Ok(*merge_kind)
                }
                MergeKind::Level1 { nominal_attached: _ } => {
                    // Merge was already specified to be level 1, error!
                    Err(TcError::MergeShouldBeLevel2 {
                        merge_term: merge_term_id,
                        offending_term: merge_element_term_id,
                    })
                }
            }
        };

        // Helper to ensure that a merge is level 1, returns the updated MergeKind.
        let ensure_merge_is_level1 = |checking_nominal: Option<TermId>| -> TcResult<MergeKind> {
            match (*merge_kind, checking_nominal) {
                (MergeKind::Unknown, _) => {
                    // Now we know that the merge should be level 1
                    Ok(MergeKind::Level1 { nominal_attached: checking_nominal })
                }
                (MergeKind::Level2, _) => {
                    // Merge was already specified to be level 2, error!
                    Err(TcError::MergeShouldBeLevel1 {
                        merge_term: merge_term_id,
                        offending_term: merge_element_term_id,
                    })
                }
                (MergeKind::Level1 { nominal_attached: _ }, None) => {
                    // Merge is level 1; independently of whether a nominal is
                    // attached, this is fine because we are not checking a nominal.
                    Ok(*merge_kind)
                }
                (MergeKind::Level1 { nominal_attached: None }, Some(checking_nominal)) => {
                    // Merge is level 1 without a nominal and we are checking a nominal; we attach
                    // the nominal.
                    Ok(MergeKind::Level1 { nominal_attached: Some(checking_nominal) })
                }
                (
                    MergeKind::Level1 { nominal_attached: Some(nominal_term_id) },
                    Some(checking_nominal),
                ) => {
                    // A nominal has already been attached, error!
                    Err(TcError::MergeShouldOnlyContainOneNominal {
                        merge_term: merge_term_id,
                        nominal_term: nominal_term_id,
                        second_nominal_term: checking_nominal,
                    })
                }
            }
        };

        // Ensure the level of the term is valid:
        match merge_element_term {
            // Type function application, access, or variable:
            // These should have already been simplified, so we only accept them if their type is
            // level 3 and the merge is level 2, which means it is a level 2 term. Their
            // type is level 2, we cannot be sure it won't have a duplicate nominal
            // definition so we cannot accept it.
            Term::AppTyFn(_) | Term::Access(_) | Term::Var(_) => {
                let ty_id_of_term = self.typer().ty_of_term(merge_element_term_id)?;
                let reader = self.reader();
                let ty_of_term = reader.get_term(ty_id_of_term);
                match ty_of_term {
                    Term::Level3(_) => {
                        // If the type of the term is level 3, then we know that the merge should be
                        // level 2:
                        *merge_kind = ensure_merge_is_level2()?;
                        Ok(())
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
            Term::Unresolved(_) => Err(TcError::NeedMoreTypeAnnotationsToResolve {
                term_to_resolve: merge_element_term_id,
            }),
            // Level 3 terms are not allowed:
            Term::Level3(_) => invalid_merge_element(),
            // Level 2 terms are allowed:
            Term::Level2(level2_term) => match level2_term {
                Level2Term::Trt(_) | Level2Term::AnyTy => {
                    *merge_kind = ensure_merge_is_level2()?;
                    Ok(())
                }
            },
            // Level 1 terms are allowed:
            Term::Level1(level1_term) => match level1_term {
                // @@Incomplete: shouldn't we also check that the `Self` property is compatible with
                // the other elements?

                // Modules:
                Level1Term::ModDef(_) => {
                    // Not checking a nominal:
                    *merge_kind = ensure_merge_is_level1(None)?;
                    Ok(())
                }
                // Nominals:
                Level1Term::NominalDef(_) => {
                    // Checking a nominal:
                    *merge_kind = ensure_merge_is_level1(Some(merge_element_term_id))?;
                    Ok(())
                }
                // Cannot attach a tuple to a merge
                // @@Design: can we possibly allow this?
                Level1Term::Tuple(_) => invalid_merge_element(),
                // Cannot attach a function type to a merge
                Level1Term::Fn(_) => invalid_merge_element(),
            },
            // Type functions are not allowed
            Term::TyFn(_) | Term::TyFnTy(_) => invalid_merge_element(),
            // Runtime terms are not allowed
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
    ///
    /// **Note**: Requires that the parameters have already been simplified.
    pub fn validate_params(&mut self, params: &Params) -> TcResult<()> {
        for param in params.positional() {
            self.validate_term(param.ty)?;
            if let Some(default_value) = param.default_value {
                self.validate_term(default_value)?;

                // Ensure the default value's type can be unified with the given type of the
                // parameter:
                let ty_of_default_value = self.typer().ty_of_simplified_term(default_value)?;
                let _ = self.unifier().unify_terms(ty_of_default_value, param.ty)?;
            }
        }
        Ok(())
    }

    /// Validate the given arguments, by validating their values.
    ///
    /// **Note**: Requires that the arguments have already been simplified.
    pub fn validate_args(&mut self, args: &Args) -> TcResult<()> {
        for arg in args.positional() {
            self.validate_term(arg.value)?;
        }
        Ok(())
    }

    /// Validate the given term for correctness.
    ///
    /// Returns the simplified term, along with its type, which are computed
    /// during the validation.
    pub fn validate_term(&mut self, term_id: TermId) -> TcResult<TermValidation> {
        // First, we try simplify the term:
        let simplified_term_id = self.simplifier().potentially_simplify_term(term_id)?;

        // Then, we try get its type:
        let term_ty_id = self.typer().ty_of_simplified_term(simplified_term_id)?;

        // If both of these succeeded, we can perform a few final checks:
        let reader = self.reader();

        // Prepare the result of the validation:
        let result = TermValidation { simplified_term_id, term_ty_id };

        let term = reader.get_term(simplified_term_id);
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

                Ok(result)
            }

            // Level 1 terms:
            Term::Level1(level1_term) => match level1_term {
                Level1Term::Tuple(tuple_ty) => {
                    // Validate each parameter
                    let tuple_ty = tuple_ty.clone();
                    self.validate_params(&tuple_ty.members)?;

                    // Ensure each parameter is runtime instantiable:
                    for param in tuple_ty.members.positional() {
                        self.ensure_term_is_runtime_instantiable(param.ty)?;
                    }
                    Ok(result)
                }
                Level1Term::Fn(fn_ty) => {
                    // Validate parameters and return type
                    let fn_ty = fn_ty.clone();
                    self.validate_params(&fn_ty.params)?;
                    self.validate_term(fn_ty.return_ty)?;

                    // Ensure each parameter and return type are runtime instantiable:
                    for param in fn_ty.params.positional() {
                        self.ensure_term_is_runtime_instantiable(param.ty)?;
                    }
                    self.ensure_term_is_runtime_instantiable(fn_ty.return_ty)?;

                    Ok(result)
                }
                Level1Term::ModDef(_) | Level1Term::NominalDef(_) => {
                    // Nothing to do, should have already been validated on creation.
                    Ok(result)
                }
            },

            // Level 0 terms:
            Term::Level0(level0_term) => match level0_term {
                Level0Term::Rt(rt_inner_term) => {
                    // Validate the inner term, and ensure it is runtime instantiable:
                    let rt_inner_term = *rt_inner_term;
                    self.validate_term(rt_inner_term)?;
                    self.ensure_term_is_runtime_instantiable(rt_inner_term)?;
                    Ok(result)
                }
                Level0Term::FnLit(fn_lit) => {
                    // Ensure the inner type is a function type, and get it:
                    let fn_lit = *fn_lit;
                    match self.term_is_fn_ty(fn_lit.fn_ty)? {
                        Some(fn_ty) => {
                            // Validate constituents:
                            let fn_ty = fn_ty;
                            self.validate_params(&fn_ty.params)?;
                            let fn_return_ty_validation = self.validate_term(fn_ty.return_ty)?;
                            let fn_return_value_validation =
                                self.validate_term(fn_lit.return_value)?;

                            // Ensure the return type of the function unifies with the type of the
                            // return value:
                            let _ = self.unifier().unify_terms(
                                fn_return_value_validation.term_ty_id,
                                fn_return_ty_validation.simplified_term_id,
                            );

                            // @@Correctness: should we not apply the above substitution somewhere?
                            Ok(result)
                        }
                        // This isn't a user error, it is a compiler error:
                        None => panic!("Found non-function type in function literal term!"),
                    }
                }
                Level0Term::EnumVariant(_) => {
                    // This should already be validated during simplification because the way enum
                    // variants get created is by simplification on access. And access
                    // simplification always checks the enum exists and contains the given variant
                    // name. Furthermore, there are no inner terms to validate.
                    Ok(result)
                }
            },

            // Access
            Term::Access(access_term) => {
                // Validate the inner term; the access should already be valid since it passed
                // the typing stage.
                self.validate_term(access_term.subject)?;
                Ok(result)
            }

            // Substitution application:
            Term::AppSub(app_sub) => {
                // @@Correctness: do we need to perform any sort of substitution validity check?
                // maybe to try unify the substitution with itself to ensure it does not
                // contradict itself? For example, if it contains cycles `T0 ->
                // T1, T1 -> T0`.
                //
                // For now, we just validate the inner term:
                self.validate_term(app_sub.term)?;
                Ok(result)
            }

            // Type function type:
            Term::TyFnTy(ty_fn_ty) => {
                // Validate the params and return type:
                let ty_fn_ty = ty_fn_ty.clone();
                self.validate_params(&ty_fn_ty.params)?;
                let _ = self.validate_term(ty_fn_ty.return_ty);

                // Ensure each parameter's type can be used as a type function parameter type:
                for param in ty_fn_ty.params.positional() {
                    if !(self.term_can_be_used_as_ty_fn_param_ty(param.ty)?) {
                        return Err(TcError::InvalidTypeFunctionParameterType {
                            param_ty: param.ty,
                        });
                    }
                }

                // Ensure the return type can be used as a type function return type:
                if !(self.term_can_be_used_as_ty_fn_return_ty(ty_fn_ty.return_ty)?) {
                    return Err(TcError::InvalidTypeFunctionParameterType {
                        param_ty: ty_fn_ty.return_ty,
                    });
                }

                Ok(result)
            }

            // Type function:
            Term::TyFn(ty_fn) => {
                // Validate params and return type.
                let ty_fn = ty_fn.clone();
                self.validate_params(&ty_fn.general_params)?;
                let general_return_validation = self.validate_term(ty_fn.general_return_ty)?;

                // We also validate the type of the type function, for including the
                // additional check of parameter type term levels:
                let _ = self.validate_term(result.term_ty_id)?;

                // Validate each case:
                for case in &ty_fn.cases {
                    self.validate_params(&case.params)?;
                    self.validate_term(case.return_ty)?;
                    self.validate_term(case.return_value)?;

                    // Ensure the params are a subtype of the general params
                    // @@ErrorReporting: might be a bit ambiguous here, perhaps we should customise
                    // the message.
                    let _ = self.unifier().unify_params(&case.params, &ty_fn.general_params)?;

                    // Ensure that the return type can be unified with the type of the return value:
                    // @@Safety: should be already simplified from above the match.
                    let return_value_ty = self.typer().ty_of_simplified_term(term_id)?;
                    let _ = self.unifier().unify_terms(case.return_ty, return_value_ty)?;

                    // Ensure the return value of each case is a subtype of the general return type.
                    let _ = self
                        .unifier()
                        .unify_terms(case.return_ty, general_return_validation.term_ty_id)?;

                    // Ensure the return value can be used as a type function return value:
                    if !(self.term_can_be_used_as_ty_fn_return_value(case.return_value)?) {
                        return Err(TcError::InvalidTypeFunctionReturnValue {
                            return_value: case.return_value,
                        });
                    }
                }

                Ok(result)
            }

            // Type function application:
            Term::AppTyFn(app_ty_fn) => {
                // Since this could be typed, it means the application is valid in terms of
                // unification of type function params with the arguments. Thus, all we need to
                // do is validate individually the term and the arguments:
                let app_ty_fn = app_ty_fn.clone();
                self.validate_term(app_ty_fn.subject)?;
                self.validate_args(&app_ty_fn.args)?;
                Ok(result)
            }
            Term::Level2(_) | Term::Level3(_) | Term::Var(_) | Term::Root | Term::Unresolved(_) => {
                // Nothing to do, should have already been validated by the typer.
                Ok(result)
            }
        }
    }

    /// Ensure that the given term is runtime instantiable.
    ///
    /// Internally uses [Self::term_is_runtime_instantiable], check its docs for
    /// info.
    pub fn ensure_term_is_runtime_instantiable(&mut self, term_id: TermId) -> TcResult<()> {
        if !(self.term_is_runtime_instantiable(term_id)?) {
            Err(TcError::TermIsNotRuntimeInstantiable { term: term_id })
        } else {
            Ok(())
        }
    }

    /// Determine whether the given term is runtime instantiable, i.e. a level 1
    /// term that can be wrapped in an Rt(..).
    ///
    /// This is the condition for the term to be able to be used within tuple
    /// types, function types, structs and enums.
    ///
    /// *Note*: assumes the term has been simplified and validated.
    pub fn term_is_runtime_instantiable(&mut self, term_id: TermId) -> TcResult<bool> {
        // Ensure that the type of the term unifies with "RuntimeInstantiable":
        let ty_id_of_term = self.typer().ty_of_simplified_term(term_id)?;
        let rt_instantiable_def = self.core_defs().runtime_instantiable_trt;
        let rt_instantiable = self.builder().create_trt_term(rt_instantiable_def);
        match self.unifier().unify_terms(ty_id_of_term, rt_instantiable) {
            Ok(_) => Ok(true),
            // We only return Ok(false) if the error is that the terms do not unify:
            Err(TcError::CannotUnify { src: _, target: _ }) => Ok(false),
            Err(err) => Err(err),
        }
    }

    /// Determine if the given term can be used as the return value of a type
    /// function.
    ///
    /// This includes constant level 0 terms, level 1 terms, level 2 terms, and
    /// other type functions.
    ///
    /// *Note*: assumes the term has been simplified and validated.
    pub fn term_can_be_used_as_ty_fn_return_value(&mut self, term_id: TermId) -> TcResult<bool> {
        // First ensure its type can be used as a return type:
        let term_ty_id = self.typer().ty_of_simplified_term(term_id)?;
        if !(self.term_can_be_used_as_ty_fn_return_ty(term_ty_id)?) {
            return Ok(false);
        }
        // If it passes the check, we just need to make sure that if it is a level 0
        // function, it is a function literal.
        let reader = self.reader();
        let term = reader.get_term(term_id);
        match term {
            Term::Level0(level0_term) => {
                match level0_term {
                    Level0Term::Rt(_) => {
                        // Not any runtime value can be used here because it might produce
                        // side-effects.
                        Ok(false)
                    }
                    Level0Term::FnLit(_) => {
                        // Function literals do not produce side effects, so they are Ok.
                        Ok(true)
                    }
                    Level0Term::EnumVariant(_) => {
                        // @@PotentiallyAllow: Enum variants also do not produce side effects, so
                        // why wouldn't they be allowed? Is there a use case for this?
                        Ok(false)
                    }
                }
            }
            _ => Ok(true),
        }
    }

    /// Determine if the given term can be used as the return type of a type
    /// function.
    ///
    /// There are also additional restrictions on the kind of *value* that can
    /// be used for a type function return, which are covered by
    /// [Self::term_can_be_used_as_ty_fn_return_value].
    ///
    /// *Note*: assumes the term has been simplified and validated.
    pub fn term_can_be_used_as_ty_fn_return_ty(&mut self, term_id: TermId) -> TcResult<bool> {
        let reader = self.reader();
        let term = reader.get_term(term_id);
        match term {
            // These have not been resolved, for now we don't allow them.
            // @@Enhance,@@ErrorReporting: we could possibly look at the type of the term?
            // Otherwise we could at least provide a better error message.
            Term::AppTyFn(_) | Term::Access(_) | Term::Var(_) => Ok(false),
            Term::Merge(terms) => {
                // Valid if each element is okay to be used as the return type:
                let terms = terms.clone();
                for term in terms {
                    if !(self.term_can_be_used_as_ty_fn_return_ty(term)?) {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Term::Level0(_) | Term::TyFn(_) => {
                // This should never happen
                unreachable!("Found type function definition or level 0 term in type position!")
            }
            Term::TyFnTy(_) => {
                // All good, basically curried type function:
                Ok(true)
            }
            Term::AppSub(app_sub) => {
                // Check the inner type:
                self.term_can_be_used_as_ty_fn_return_ty(app_sub.term)
            }
            Term::Unresolved(_) => {
                // More type annotations are needed
                Err(TcError::NeedMoreTypeAnnotationsToResolve { term_to_resolve: term_id })
            }
            // All level 2 and 3 terms are ok to use as return types
            Term::Level2(_) | Term::Level3(_) => Ok(true),
            // All level 1 terms are ok to use as return types, but their values have some
            // constraints (see `Self::term_can_be_used_as_ty_fn_return_value` function above)
            Term::Level1(_) => Ok(true),
            Term::Root => {
                // This should be okay, for example if we are returning some TyFnTy value.
                Ok(true)
            }
        }
    }

    /// Determine if the given term can be used as the parameter type of a type
    /// function.
    ///
    /// This extends to level 2, as well as type function types returning level
    /// 2 terms. **Note**: assumes the term has been simplified.
    ///
    /// @@Extension: we could allow level 3 terms as parameters too (TraitKind).
    pub fn term_can_be_used_as_ty_fn_param_ty(&mut self, term_id: TermId) -> TcResult<bool> {
        let reader = self.reader();
        let term = reader.get_term(term_id);
        match term {
            // These have not been resolved, for now we don't allow them.
            // @@Enhance,@@ErrorReporting: we could possibly look at the type of the term?
            // Otherwise we could at least provide a better error message.
            Term::AppTyFn(_) | Term::Access(_) | Term::Var(_) => Ok(false),
            Term::Merge(terms) => {
                // Valid if each element is okay to be used as a parameter type:
                let terms = terms.clone();
                for term in terms {
                    if !(self.term_can_be_used_as_ty_fn_param_ty(term)?) {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Term::Level0(_) | Term::TyFn(_) => {
                // This should never happen
                unreachable!("Found type function definition or level 0 term in type position!")
            }
            Term::TyFnTy(ty_fn_ty) => {
                // Type function types are okay to use if their return types can be used here:
                self.term_can_be_used_as_ty_fn_param_ty(ty_fn_ty.return_ty)
            }
            Term::AppSub(app_sub) => {
                // Check the inner type:
                self.term_can_be_used_as_ty_fn_return_ty(app_sub.term)
            }
            Term::Unresolved(_) => {
                // More type annotations are needed
                Err(TcError::NeedMoreTypeAnnotationsToResolve { term_to_resolve: term_id })
            }
            // All level 2 and 3 terms are ok to use as parameter types
            Term::Level2(_) | Term::Level3(_) => Ok(true),
            // Level 1 terms are not ok (because their instances are runtime)
            Term::Level1(_) => Ok(false),
            Term::Root => {
                // @@PotentiallyUnnecessary: is there some use case to allow this?
                Ok(false)
            }
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
    /// That is, if for any term X, they produce the same result when applied to
    /// X
    ///
    /// @@Correctness: This is not based on any accepted algorithm, and requires
    /// testing to ensure its correctness.
    pub fn subs_are_equivalent(&mut self, s0: &Sub, s1: &Sub) -> bool {
        // First we get the two substitutions as lists sorted by their domains:
        let mut s0_list = s0.pairs().collect::<Vec<_>>();
        let mut s1_list = s1.pairs().collect::<Vec<_>>();
        s0_list.sort_by_key(|x| x.0);
        s1_list.sort_by_key(|x| x.0);

        // Then for each pair, we ensure the domain elements are the same, and the range
        // elements can be unified:
        for (s0_element, s1_element) in s0_list.iter().zip(&s1_list) {
            if s0_element.0 != s1_element.0 {
                return false;
            }

            // Unify bidirectionally
            if self.unifier().unify_terms(s0_element.1, s1_element.1).is_err()
                || self.unifier().unify_terms(s1_element.1, s0_element.1).is_err()
            {
                return false;
            }
        }

        // If all succeeded, the substitutions are equivalent!
        true
    }
}
