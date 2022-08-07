//! Contains utilities to validate terms.
use hash_utils::store::Store;

use super::AccessToOps;
use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        macros::{tc_panic, tc_panic_on_many},
        params::ParamListKind,
    },
    ops::params::validate_param_list_ordering,
    storage::{
        arguments::ArgsId,
        mods::ModDefId,
        nominals::NominalDefId,
        params::ParamsId,
        primitives::{
            ConstructedTerm, FnTy, Level0Term, Level1Term, Level2Term, Member, ModDefOrigin,
            NominalDef, Scope, ScopeKind, StructFields, Term,
        },
        scope::ScopeId,
        terms::{TermId, TermStore},
        trts::TrtDefId,
        AccessToStorage, StorageRef,
    },
};
use std::fmt::Display;

/// Represents the level of a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// A enumeration of the level kinds that terms can be.
pub enum TermLevel {
    /// Couldn't be determined and thus labelled as unknown
    Unknown,
    /// Level 0 terms
    Level0,
    /// Level 1 terms
    Level1,
    /// Level 2 terms
    Level2,
    /// Level 3 terms
    Level3,
    /// Level 4 terms, specifically [Term::Root]
    Level4,
}

impl Display for TermLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TermLevel::Unknown => write!(f, "unknown"),
            TermLevel::Level0 => write!(f, "level-0"),
            TermLevel::Level1 => write!(f, "level-1"),
            TermLevel::Level2 => write!(f, "level-2"),
            TermLevel::Level3 => write!(f, "level-3"),
            TermLevel::Level4 => write!(f, "level-4"),
        }
    }
}

impl Term {
    /// Compute the level of the term. This is a primitive computation
    /// and does not attempt to compute the true level of the [Term]
    /// by looking at the inner children of the [Term].
    pub fn get_term_level(&self, _store: &TermStore) -> TermLevel {
        // @@Todo(feds01): implement the other variants by recursing into them.
        // This should be done on a struct with access to storage
        match self {
            Term::Access(_)
            | Term::Var(_)
            | Term::Merge(_)
            | Term::TyFn(_)
            | Term::TyOf(_)
            | Term::Union(_)
            | Term::SetBound(_)
            | Term::ScopeVar(_)
            | Term::BoundVar(_)
            | Term::TyFnTy(_)
            | Term::TyFnCall(_) => TermLevel::Unknown,
            Term::Unresolved(_) => TermLevel::Unknown,
            Term::Root => TermLevel::Level4,
            Term::Level3(_) => TermLevel::Level3,
            Term::Level2(_) => TermLevel::Level2,
            Term::Level1(_) => TermLevel::Level1,
            Term::Level0(_) => TermLevel::Level0,
        }
    }
}

/// Can resolve the type of a given term, as another term.
pub struct Validator<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for Validator<'tc> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
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
    Allowed,
    Required,
}

impl<'tc> Validator<'tc> {
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Validate the members of the given constant scope.
    ///
    /// Allows uninitialised members in the scope if `allow_uninitialised` is
    /// true.
    fn validate_constant_scope(
        &self,
        scope_id: ScopeId,
        allow_uninitialised: bool,
    ) -> TcResult<()> {
        // @@Design: when do we insert each member into the scope? As we go or all at
        // once? For now, we insert as we go.

        // Enter the progressive scope:
        let progressive_scope = Scope::new(ScopeKind::Constant, []);
        let progressive_scope_id = self.scope_store().create(progressive_scope);
        self.scope_manager().enter_scope(progressive_scope_id, |this| {
            // @@Performance: sad that we have to clone here:
            let scope = this.reader().get_scope(scope_id);
            for member in scope.iter() {
                // Add the member to the progressive scope so that this and next members can
                // access it.
                this.scope_store().modify_fast(progressive_scope_id, |scope| scope.add(member));

                // Initialisation check
                if !allow_uninitialised {
                    match member {
                        Member::Constant(constant_member) if constant_member.value().is_none() => {
                            return Err(TcError::UninitialisedMemberNotAllowed {
                                member_ty: member.ty(),
                            });
                        }
                        _ => {}
                    }
                }

                // Validate the member:
                match member.value() {
                    None => {
                        // Validate only the type
                        this.validator().validate_term(member.ty())?;
                    }
                    Some(value) => {
                        // Validate the term, the type, and unify them.
                        let TermValidation { term_ty_id, .. } =
                            this.validator().validate_term(value)?;
                        let TermValidation { simplified_term_id: simplified_ty_id, .. } =
                            this.validator().validate_term(member.ty())?;
                        let _ = this.unifier().unify_terms(term_ty_id, simplified_ty_id)?;
                    }
                }

                // @@Incomplete: here we also need to ensure that the member
                // does not directly access itself (i.e. `a := a`).
            }

            Ok(())
        })
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
        &self,
        trt_def_term_id: TermId,
        scope_originating_term_id: TermId,
        scope_id: ScopeId,
    ) -> TcResult<()> {
        let scope = self.reader().get_scope(scope_id);

        // Simplify the term and ensure it is a trait
        let simplified_trt_def_term_id =
            self.simplifier().potentially_simplify_term(trt_def_term_id)?;
        let reader = self.reader();
        let simplified_trt_def_term = reader.get_term(simplified_trt_def_term_id);

        // Ensure the term leads to a trait definition:
        match simplified_trt_def_term {
            Term::SetBound(set_bound) => {
                self.scope_manager().enter_scope(set_bound.scope, |this| {
                    this.validator().ensure_scope_implements_trait(
                        set_bound.term,
                        scope_originating_term_id,
                        scope_id,
                    )
                })
            }
            Term::Level2(Level2Term::Trt(trt_def_id)) => {
                let trt_def_members = self.reader().get_trt_def(trt_def_id).members;
                // @@Performance: cloning :((
                let trt_def_members = self.reader().get_scope(trt_def_members);

                // Ensure all members have been implemented:
                for trt_member in trt_def_members.iter() {
                    if let Some((scope_member, _)) = scope.get(trt_member.name()) {
                        let _ = self.unifier().unify_terms(scope_member.ty(), trt_member.ty())?;
                    } else {
                        return Err(TcError::TraitImplMissingMember {
                            trt_def_term_id,
                            trt_impl_term_id: scope_originating_term_id,
                            trt_def_missing_member_term_id: trt_member.ty(),
                        });
                    }
                }

                // @@Design: do we want to block the implementation of members
                // that are not in the trait definition?
                Ok(())
            }
            _ => Err(TcError::CannotImplementNonTrait { term: simplified_trt_def_term_id }),
        }
    }

    /// Validate the module definition of the given [ModDefId], defined in
    /// `originating_term_id`.
    pub(crate) fn validate_mod_def(
        &self,
        mod_def_id: ModDefId,
        originating_term_id: TermId,
        allow_uninitialised: bool,
    ) -> TcResult<()> {
        let reader = self.reader();
        let mod_def = reader.get_mod_def(mod_def_id);
        let mod_def_members = mod_def.members;
        let mod_def_origin = mod_def.origin;

        // Validate all members:
        // Bound vars should already be in scope.
        self.validate_constant_scope(mod_def_members, allow_uninitialised)?;

        // Ensure if it is a trait impl it implements all the trait members.
        if let ModDefOrigin::TrtImpl(trt_def_term_id) = mod_def_origin {
            self.ensure_scope_implements_trait(
                trt_def_term_id,
                originating_term_id,
                mod_def_members,
            )?;
        }

        Ok(())
    }

    /// Validate the trait definition of the given [TrtDefId]
    pub(crate) fn validate_trt_def(&self, trt_def_id: TrtDefId) -> TcResult<()> {
        // @@Design: do we allow traits without self?
        let reader = self.reader();
        let trt_def = reader.get_trt_def(trt_def_id);
        self.validate_constant_scope(trt_def.members, true)
    }

    /// Validate the nominal definition of the given [NominalDefId]
    pub(crate) fn validate_nominal_def(&self, nominal_def_id: NominalDefId) -> TcResult<()> {
        match self.nominal_def_store().get(nominal_def_id) {
            NominalDef::Struct(struct_def) => {
                // Ensure all members types of the fields for the struct are
                // runtime-instantiable by ensuring that the type of the field
                // term implements the rti trait.
                if let StructFields::Explicit(fields_id) = struct_def.fields {
                    let fields = self.params_store().get_owned_param_list(fields_id);

                    // Validate the ordering and the number of times parameter field names
                    // are specified, although the ordering shouldn't matter
                    validate_param_list_ordering(&fields, ParamListKind::Params(fields_id))?;

                    // Validate all fields of an struct def implement `SizedTy`
                    let rti_trt = self.builder().create_sized_ty_term();
                    for field in fields.positional().iter() {
                        let field_ty = self.typer().infer_ty_of_term(field.ty)?;
                        self.unifier().unify_terms(field_ty, rti_trt)?;
                    }
                }

                Ok(())
            }
            NominalDef::Enum(enum_def) => {
                for (_, variant) in enum_def.variants.iter() {
                    let variant_fields = self.params_store().get_owned_param_list(variant.fields);

                    // Validate the ordering and the number of times parameter field names
                    // are specified, although the ordering shouldn't matter
                    //
                    // @@Unnecessary?
                    validate_param_list_ordering(
                        &variant_fields,
                        ParamListKind::Params(variant.fields),
                    )?;

                    // Validate all fields of an struct def implement `SizedTy`
                    let sized_ty = self.builder().create_sized_ty_term();

                    for field in variant_fields.positional().iter() {
                        let field_ty = self.typer().infer_ty_of_term(field.ty)?;
                        self.unifier().unify_terms(field_ty, sized_ty)?;
                    }
                }

                Ok(())
            }
        }
    }

    /// Ensure the element `union_element_term_id` of the union with the given
    /// `union_term_id` is level 1, with each element containing 1 nominal.
    pub(crate) fn validate_union_element(
        &self,
        union_term_id: TermId,
        union_element_term_id: TermId,
    ) -> TcResult<()> {
        let reader = self.reader();
        let union_element_term = reader.get_term(union_element_term_id);

        // Error helper:
        let invalid_union_element = || -> TcResult<()> {
            Err(TcError::InvalidUnionElement { term: union_element_term_id })
        };

        // Ensure the level of the term is valid:
        match union_element_term {
            Term::SetBound(set_bound) => {
                // Ensure the inner one is valid
                self.scope_manager().enter_scope(set_bound.scope, |this| {
                    this.validator().validate_union_element(union_term_id, set_bound.term)
                })
            }
            Term::Level1(level1_term) => match level1_term {
                // Checking a nominal
                Level1Term::NominalDef(_) => Ok(()),
                // Not checking a nominal:
                Level1Term::Tuple(_) | Level1Term::Fn(_) | Level1Term::ModDef(_) => {
                    invalid_union_element()
                }
            },
            Term::ScopeVar(scope_var) => {
                // Forward to the value:
                let member = self.scope_manager().get_scope_var_member(scope_var);
                let value = member.member.value();
                if let Some(value) = value {
                    self.validate_union_element(union_term_id, value)
                } else {
                    // @@Todo: we could allow this?
                    invalid_union_element()
                }
            },
            // Unclear if this fits the requirements, so we reject it:
            Term::Unresolved(_) => {
                Err(TcError::NeedMoreTypeAnnotationsToResolve { term: union_element_term_id })
            }
            Term::Merge(_)
            | Term::Level3(_)
            | Term::Level2(_)
            | Term::TyFn(_)
            | Term::TyFnTy(_)
            | Term::Level0(_)
            | Term::Root
            | Term::TyOf(_)
            | Term::TyFnCall(_)
            | Term::Access(_)
            | Term::BoundVar(_) // @@Todo: we could allow this? Similar to merge elements where we just get their type..
            | Term::Var(_) => invalid_union_element(),
            // This should have been flattened already:
            Term::Union(_) => {
                tc_panic_on_many!(
                    [union_element_term_id, union_term_id],
                    self,
                    "Union term should have already been flattened"
                )
            }
        }
    }

    /// Ensure the element `merge_element_term_id` of the merge with the given
    /// `merge_term_id` is either level 2 (along with the merge being all
    /// level 2), or level 1 (along with the merge being all level 1).
    /// Furthermore, if it is level 1, the merge should only have zero or one
    /// nominal definition attached.
    fn validate_merge_element(
        &self,
        merge_kind: &mut MergeKind,
        merge_term_id: TermId,
        merge_element_term_id: TermId,
    ) -> TcResult<()> {
        let reader = self.reader();
        let merge_element_term = reader.get_term(merge_element_term_id);

        // Error helper:
        let invalid_merge_element = || -> TcResult<()> {
            Err(TcError::InvalidMergeElement { term: merge_element_term_id })
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
                    Err(TcError::MergeShouldBeLevel1 {
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
                    Err(TcError::MergeShouldBeLevel2 {
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
                        initial_term: nominal_term_id,
                        offending_term: checking_nominal,
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
            Term::ScopeVar(_)
            | Term::BoundVar(_)
            | Term::TyFnCall(_)
            | Term::Access(_)
            | Term::Var(_) => {
                let ty_id_of_term = self.typer().infer_ty_of_term(merge_element_term_id)?;
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
            Term::SetBound(set_bound) => {
                // Ensure the inner one is valid
                self.scope_manager().enter_scope(set_bound.scope, |this| {
                    this.validator().validate_merge_element(
                        merge_kind,
                        merge_term_id,
                        set_bound.term,
                    )
                })
            }
            // Unclear if this fits the requirements, so we reject it:
            Term::Unresolved(_) => {
                Err(TcError::NeedMoreTypeAnnotationsToResolve { term: merge_element_term_id })
            }
            // Union allowed if each inner term is allowed
            Term::Union(terms) => {
                let mut initial_merge_kind = *merge_kind;
                let terms = terms;
                for term_id in terms.iter() {
                    self.validate_merge_element(&mut initial_merge_kind, merge_term_id, *term_id)?;
                }
                ensure_merge_is_level1(Some(merge_element_term_id))?;
                Ok(())
            }
            // Level 3 terms are not allowed:
            Term::Level3(_) => invalid_merge_element(),
            // Level 2 terms are allowed:
            Term::Level2(level2_term) => match level2_term {
                Level2Term::Trt(_) | Level2Term::AnyTy | Level2Term::SizedTy => {
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
                // Nominals, tuples, functions:
                Level1Term::NominalDef(_) | Level1Term::Tuple(_) | Level1Term::Fn(_) => {
                    *merge_kind = ensure_merge_is_level1(Some(merge_element_term_id))?;
                    Ok(())
                }
            },
            // Type functions are not allowed
            Term::TyFn(_) | Term::TyFnTy(_) => invalid_merge_element(),
            // Runtime terms are not allowed
            Term::Level0(_) => invalid_merge_element(),
            // Root is not allowed
            Term::Root => invalid_merge_element(),
            // Unsimplifiable typeof is not allowed
            Term::TyOf(_) => invalid_merge_element(),
            // This should have been flattened already:
            Term::Merge(_) => {
                tc_panic_on_many!(
                    [merge_element_term_id, merge_term_id],
                    self,
                    "Merge term should have already been flattened"
                )
            }
        }
    }

    /// Validate the given parameters, by validating their types and values,
    /// positions within all of the parameters, and re-use of already
    /// declared parameter names.
    ///
    /// **Note**: Requires that the parameters have already been simplified.
    pub(crate) fn validate_params(&self, params_id: ParamsId) -> TcResult<()> {
        let params = self.params_store().get_owned_param_list(params_id);
        validate_param_list_ordering(&params, ParamListKind::Params(params_id))?;

        for param in params.positional() {
            self.validate_term(param.ty)?;

            if let Some(default_value) = param.default_value {
                self.validate_term(default_value)?;

                // Ensure the default value's type can be unified with the given type of the
                // parameter:
                let ty_of_default_value =
                    self.typer().infer_ty_of_simplified_term(default_value)?;
                let _ = self.unifier().unify_terms(ty_of_default_value, param.ty)?;
            }
        }
        Ok(())
    }

    /// Validate the given arguments, by validating their values.
    ///
    /// **Note**: Requires that the arguments have already been simplified.
    pub(crate) fn validate_args(&self, args_id: ArgsId) -> TcResult<()> {
        let args = self.args_store().get_owned_param_list(args_id);

        for arg in args.positional() {
            self.validate_term(arg.value)?;
        }
        Ok(())
    }

    /// Validate the given term for correctness.
    ///
    /// Returns the simplified term, along with its type, which are computed
    /// during the validation.
    pub(crate) fn validate_term(&self, term_id: TermId) -> TcResult<TermValidation> {
        // Check if we have already performed a simplification on this term, if so
        // return the result.
        if let Some(term) = self.cacher().has_been_validated(term_id) {
            return Ok(term);
        }

        // First, we try simplify the term:
        let simplified_term_id = self.simplifier().potentially_simplify_term(term_id)?;

        // Then, we try get its type:
        let term_ty_id = self.typer().infer_ty_of_simplified_term(simplified_term_id)?;

        // If both of these succeeded, we can perform a few final checks:
        let reader = self.reader();

        // Prepare the result of the validation:
        let result = TermValidation { simplified_term_id, term_ty_id };

        let term = reader.get_term(simplified_term_id);

        let validated_term = match term {
            // Merge:
            Term::Merge(terms) => {
                if let [term] = terms.as_slice() {
                    // Shortcut: single term:
                    self.validate_term(*term)
                } else {
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
            }

            // Union
            Term::Union(terms) => {
                if let [term] = terms.as_slice() {
                    // Shortcut: single term:
                    self.validate_term(*term)
                } else {
                    // First, validate each term:
                    let terms = terms.clone();
                    for term in terms.iter().copied() {
                        self.validate_term(term)?;
                    }

                    // Validate the level of each term against the union restrictions (see
                    // [Self::validate_union_element] docs).
                    for union_element_term_id in terms.iter().copied() {
                        self.validate_union_element(simplified_term_id, union_element_term_id)?;
                    }

                    Ok(result)
                }
            }

            // Level 1 terms:
            Term::Level1(level1_term) => match level1_term {
                Level1Term::Tuple(tuple_ty) => {
                    // Validate each parameter
                    self.validate_params(tuple_ty.members)?;

                    let members = self.params_store().get_owned_param_list(tuple_ty.members);

                    // Ensure each parameter is runtime instantiable:
                    for param in members.positional() {
                        self.ensure_term_is_runtime_instantiable(param.ty)?;
                    }
                    Ok(result)
                }
                Level1Term::Fn(fn_ty) => {
                    // Validate parameters and return type
                    self.validate_params(fn_ty.params)?;
                    self.validate_term(fn_ty.return_ty)?;

                    let params = self.params_store().get_owned_param_list(fn_ty.params);

                    // Ensure each parameter and return type are runtime instantiable:
                    for param in params.positional() {
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
                    self.validate_term(rt_inner_term)?;
                    self.ensure_term_is_runtime_instantiable(rt_inner_term)?;
                    Ok(result)
                }
                Level0Term::FnLit(fn_lit) => {
                    // Ensure the inner type is a function type, and get it:
                    match self.term_is_fn_ty(fn_lit.fn_ty)? {
                        Some(fn_ty) => {
                            // Validate constituents:
                            let fn_ty = fn_ty;
                            self.validate_params(fn_ty.params)?;
                            let fn_return_ty_validation = self.validate_term(fn_ty.return_ty)?;
                            let fn_return_value_validation =
                                self.validate_term(fn_lit.return_value)?;

                            // Ensure the return type of the function unifies with the type of the
                            // return value:
                            let _ = self.unifier().unify_terms(
                                fn_return_value_validation.term_ty_id,
                                fn_return_ty_validation.simplified_term_id,
                            )?;

                            // @@Correctness: should we not apply the above substitution somewhere?
                            Ok(result)
                        }
                        // This isn't a user error, it is a compiler error:
                        None => tc_panic!(
                            simplified_term_id,
                            self,
                            "Found non-function type in function literal term!"
                        ),
                    }
                }
                Level0Term::Constructed(ConstructedTerm { subject, members }) => {
                    // Ensure the subject of the term is constructable
                    if !self.simplifier().is_term_constructable(subject) {
                        Err(TcError::InvalidCallSubject { term: subject })
                    } else {
                        // There must be exactly one constructor
                        let (_, variants) =
                            self.typer().infer_constructors_of_nominal_term(simplified_term_id)?[0];

                        self.validate_args(members)?;
                        let _ = self
                            .unifier()
                            .unify_params_with_args(variants, members, term_id, subject)?;

                        Ok(result)
                    }
                }
                Level0Term::EnumVariant(_) => {
                    // This should already be validated during simplification because the way enum
                    // variants get created is by simplification on access. And access
                    // simplification always checks the enum exists and contains the given variant
                    // name. Furthermore, there are no inner terms to validate.
                    Ok(result)
                }
                Level0Term::FnCall(_) => {
                    tc_panic!(
                        simplified_term_id,
                        self,
                        "Function call in validation should have been simplified!"
                    )
                }
                Level0Term::Lit(_) => {
                    // @@Todo: ensure that integers are not too large
                    Ok(result)
                }
                Level0Term::Tuple(tuple_lit) => {
                    self.validate_args(tuple_lit.members)?;
                    // Validate its type to ensure members are runtime instantiable:
                    self.validate_term(term_ty_id)?;
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

            // Set bound, just validate inner
            Term::SetBound(set_bound) => {
                let _ = self.scope_manager().enter_scope(set_bound.scope, |this| {
                    this.validator().validate_term(set_bound.term)
                })?;
                Ok(result)
            }

            // Type function type:
            Term::TyFnTy(ty_fn_ty) => {
                // Validate the params and return type:
                let ty_fn_ty = ty_fn_ty;
                self.validate_params(ty_fn_ty.params)?;

                let param_scope = self.scope_manager().make_bound_scope(ty_fn_ty.params);
                self.scope_manager().enter_scope(param_scope, |this| {
                    let _ = this.validator().validate_term(ty_fn_ty.return_ty)?;
                    let params =
                        this.validator().params_store().get_owned_param_list(ty_fn_ty.params);

                    // Ensure each parameter's type can be used as a type function parameter type:
                    for param in params.positional() {
                        if !(this.validator().term_can_be_used_as_ty_fn_param_ty(param.ty)?) {
                            return Err(TcError::InvalidTyFnParamTy { param_ty: param.ty });
                        }
                    }

                    // Ensure the return type can be used as a type function return type:
                    if !(this
                        .validator()
                        .term_can_be_used_as_ty_fn_return_ty(ty_fn_ty.return_ty)?)
                    {
                        return Err(TcError::InvalidTyFnParamTy { param_ty: ty_fn_ty.return_ty });
                    }
                    Ok(())
                })?;

                Ok(result)
            }

            // Type function:
            Term::TyFn(ty_fn) => {
                // Validate params and return type.
                let ty_fn = ty_fn;
                self.validate_params(ty_fn.general_params)?;

                // Enter param scope:
                let param_scope = self.scope_manager().make_bound_scope(ty_fn.general_params);
                let general_return_validation =
                    self.scope_manager().enter_scope(param_scope, |this| {
                        let general_return_validation =
                            this.validator().validate_term(ty_fn.general_return_ty)?;

                        // We also validate the type of the type function, for including the
                        // additional check of parameter type term levels:
                        let _ = this.validator().validate_term(result.term_ty_id)?;

                        Ok(general_return_validation)
                    })?;

                // Validate each case:
                for case in &ty_fn.cases {
                    self.validate_params(case.params)?;

                    let param_scope = self.scope_manager().make_bound_scope(case.params);
                    self.scope_manager().enter_scope(param_scope, |this| {
                        this.validator().validate_term(case.return_ty)?;
                        this.validator().validate_term(case.return_value)?;

                        // Ensure the params are a subtype of the general params
                        //
                        // @@ErrorReporting: might be a bit ambiguous here, perhaps we should
                        // customise the message.
                        //
                        // @@Correctness: Is it ok to use `return_ty` of the case as the target, and
                        // `term_id` as the source??
                        let _ = this.validator().unifier().unify_params(
                            case.params,
                            ty_fn.general_params,
                            case.return_ty,
                            term_id,
                        )?;

                        // Ensure that the return type can be unified with the type of the return
                        // value: @@Safety: should be already simplified
                        // from above the match.
                        let return_value_ty = this
                            .validator()
                            .typer()
                            .infer_ty_of_simplified_term(case.return_value)?;
                        let _ = this
                            .validator()
                            .unifier()
                            .unify_terms(return_value_ty, case.return_ty)?;

                        // Ensure the return value of each case is a subtype of the general return
                        // type.
                        let _ = this.validator().unifier().unify_terms(
                            case.return_ty,
                            general_return_validation.simplified_term_id,
                        )?;

                        // Ensure the return value can be used as a type function return value:
                        if !(this
                            .validator()
                            .term_can_be_used_as_ty_fn_return_value(case.return_value)?)
                        {
                            return Err(TcError::InvalidTyFnReturnValue {
                                return_value: case.return_value,
                            });
                        }

                        Ok(())
                    })?;
                }

                Ok(result)
            }

            // Typeof: recurse to inner
            Term::TyOf(term) => self.validate_term(term),

            // Type function application:
            Term::TyFnCall(app_ty_fn) => {
                // Since this could be typed, it means the application is valid in terms of
                // unification of type function params with the arguments. Thus, all we need to
                // do is validate individually the term and the arguments:
                let app_ty_fn = app_ty_fn;
                self.validate_term(app_ty_fn.subject)?;
                self.validate_args(app_ty_fn.args)?;
                Ok(result)
            }
            Term::ScopeVar(_) => Ok(result),
            Term::BoundVar(_) => {
                // @@Todo: ensure bound var exists
                Ok(result)
            }
            Term::Level2(_) | Term::Level3(_) | Term::Var(_) | Term::Root | Term::Unresolved(_) => {
                // Nothing to do, should have already been validated by the typer.
                Ok(result)
            }
        }?;

        // Add an entry into the validation cache
        self.cacher().add_validation_entry(term_id, validated_term);
        Ok(validated_term)
    }

    /// Ensure that the given term is runtime instantiable.
    ///
    /// Internally uses [Self::term_is_runtime_instantiable], check its docs for
    /// info.
    pub(crate) fn ensure_term_is_runtime_instantiable(&self, term_id: TermId) -> TcResult<()> {
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
    pub(crate) fn term_is_runtime_instantiable(&self, term_id: TermId) -> TcResult<bool> {
        // Ensure that the type of the term unifies with "SizedTy":
        let ty_id_of_term = self.typer().infer_ty_of_simplified_term(term_id)?;
        let rt_instantiable_trt = self.builder().create_sized_ty_term();
        match self.unifier().unify_terms(ty_id_of_term, rt_instantiable_trt) {
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
    pub(crate) fn term_can_be_used_as_ty_fn_return_value(&self, term_id: TermId) -> TcResult<bool> {
        // First ensure its type can be used as a return type:
        let term_ty_id = self.typer().infer_ty_of_simplified_term(term_id)?;
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
                    Level0Term::FnCall(_) => {
                        tc_panic!(
                        term_id,
                        self,
                        "Function call in checking for type function return validity should have been simplified!"
                    )
                    }
                    Level0Term::Lit(_) | Level0Term::Tuple(_) | Level0Term::Constructed(_) => {
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
    pub(crate) fn term_can_be_used_as_ty_fn_return_ty(&self, term_id: TermId) -> TcResult<bool> {
        let reader = self.reader();
        let term = reader.get_term(term_id);
        match term {
            // These have not been resolved, for now we don't allow them.
            // @@Enhance,@@ErrorReporting: we could possibly look at the type of the term?
            // Otherwise we could at least provide a better error message.
            Term::ScopeVar(_)
            | Term::BoundVar(_)
            | Term::TyOf(_)
            | Term::TyFnCall(_)
            | Term::Access(_)
            | Term::Var(_) => Ok(false),
            Term::Merge(terms) | Term::Union(terms) => {
                // Valid if each element is okay to be used as the return type:
                let terms = terms;
                for term in terms {
                    if !(self.term_can_be_used_as_ty_fn_return_ty(term)?) {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Term::Level0(_) | Term::TyFn(_) => {
                // This should never happen
                tc_panic!(
                    term_id,
                    self,
                    "Found type function definition or level 0 term in type position!"
                )
            }
            Term::TyFnTy(_) => {
                // All good, basically curried type function:
                Ok(true)
            }
            Term::SetBound(set_bound) => {
                // Look at inner term
                self.scope_manager().enter_scope(set_bound.scope, |this| {
                    this.validator().term_can_be_used_as_ty_fn_return_ty(set_bound.term)
                })
            }
            Term::Unresolved(_) => {
                // More type annotations are needed
                Err(TcError::NeedMoreTypeAnnotationsToResolve { term: term_id })
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
    pub(crate) fn term_can_be_used_as_ty_fn_param_ty(&self, term_id: TermId) -> TcResult<bool> {
        let reader = self.reader();
        let term = reader.get_term(term_id);
        match term {
            // These have not been resolved, for now we don't allow them.
            // @@Enhance,@@ErrorReporting: we could possibly look at the type of the term?
            // Otherwise we could at least provide a better error message.
            Term::ScopeVar(_)
            | Term::BoundVar(_)
            | Term::TyFnCall(_)
            | Term::Access(_)
            | Term::Var(_) => Ok(false),
            Term::Union(terms) | Term::Merge(terms) => {
                // Valid if each element is okay to be used as a parameter type:
                let terms = terms;
                for term in terms {
                    if !(self.term_can_be_used_as_ty_fn_param_ty(term)?) {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Term::Level0(_) | Term::TyFn(_) => {
                // This should never happen
                tc_panic!(
                    term_id,
                    self,
                    "Found type function definition or level 0 term in type position!"
                )
            }
            Term::TyFnTy(ty_fn_ty) => {
                // Type function types are okay to use if their return types can be used here:
                self.term_can_be_used_as_ty_fn_param_ty(ty_fn_ty.return_ty)
            }
            Term::SetBound(set_bound) => {
                // Look at inner term
                self.scope_manager().enter_scope(set_bound.scope, |this| {
                    this.validator().term_can_be_used_as_ty_fn_param_ty(set_bound.term)
                })
            }
            Term::Unresolved(_) => {
                // More type annotations are needed
                Err(TcError::NeedMoreTypeAnnotationsToResolve { term: term_id })
            }
            // All level 2 and 3 terms are ok to use as parameter types
            Term::Level2(_) | Term::Level3(_) => Ok(true),
            // Level 1 terms are not ok (because their instances are runtime)
            Term::Level1(_) => Ok(false),
            Term::TyOf(_) | Term::Root => {
                // @@PotentiallyUnnecessary: is there some use case to allow this?
                Ok(false)
            }
        }
    }

    /// Determine if the given term is a function type, and if so return it.
    pub(crate) fn term_is_fn_ty(&self, term_id: TermId) -> TcResult<Option<FnTy>> {
        let simplified_term_id = self.simplifier().potentially_simplify_term(term_id)?;
        let reader = self.reader();
        let term = reader.get_term(simplified_term_id);
        match term {
            Term::Level1(Level1Term::Fn(fn_ty)) => Ok(Some(fn_ty)),
            _ => Ok(None),
        }
    }
}
