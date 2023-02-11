//! Contains operations to get the type of a term.
use hash_ast::ast::ParamOrigin;
use hash_source::{constant::CONSTANT_MAP, identifier::Identifier};
use hash_tir::{
    args::{Arg, ArgsId},
    mods::ModDefOrigin,
    nominals::{NominalDef, StructFields},
    params::{AccessOp, Param, ParamsId},
    pats::{AccessPat, ArrayPat, ConstPat, Pat, PatArgsId, PatId, RangePat},
    scope::Member,
    terms::{
        ConstructedTerm, Level0Term, Level1Term, Level2Term, Level3Term, LitTerm, Term, TermId,
    },
};
use hash_utils::itertools::Itertools;

use super::{params::pair_args_with_params, AccessToOps};
use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        macros::tc_panic,
    },
    storage::{AccessToStorage, StorageRef},
};

/// Can resolve the type of a given term, as another term.
pub struct Typer<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for Typer<'tc> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

/// A version of member data where the type has been inferred if it was not
/// given in the member definition.
#[derive(Debug, Clone, Copy)]
pub struct InferredMemberData {
    pub ty: TermId,
    pub value: Option<TermId>,
}

impl<'tc> Typer<'tc> {
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Get the type of the given term, as another term. This will copy over the
    /// location of the provided term to the new term within
    /// [hash_tir::location::LocationStore].
    ///
    /// First simplifies the term. If you already know you have a simplified
    /// term, you can use [`Typer::infer_ty_of_simplified_term`].
    pub(crate) fn infer_ty_of_term(&self, term: TermId) -> TcResult<TermId> {
        if let Some(inferred_term) = self.cacher().has_been_inferred(term) {
            return Ok(inferred_term);
        }

        let simplified_term_id = self.simplifier().potentially_simplify_term(term)?;
        let new_term = self.infer_ty_of_simplified_term(simplified_term_id)?;

        // Record an entry in the cache about the inferred term
        self.cacher().add_inference_entry(term, new_term);
        Ok(new_term)
    }

    /// Get the type of the given term, given that it is simplified, as another
    /// term.
    ///
    /// **Warning**: This might produce unexpected behaviour if the term is not
    /// simplified.
    pub(crate) fn infer_ty_of_simplified_term(&self, term_id: TermId) -> TcResult<TermId> {
        let term = self.reader().get_term(term_id);
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
                        // Unify the type function type params with the given args:
                        let ty_fn_ty = ty_fn_ty;
                        let _ = self.unifier().unify_params_with_args(
                            ty_fn_ty.params,
                            app_ty_fn.args,
                            term_id,
                            ty_id_of_subject,
                        )?;
                        let scope = self.scope_manager().make_set_bound_scope(
                            ty_fn_ty.params,
                            app_ty_fn.args,
                            term_id,
                            ty_id_of_subject,
                        );

                        // Apply the substitution to the return type and use it as the result:
                        Ok(self
                            .discoverer()
                            .potentially_apply_set_bound_to_term(scope, ty_fn_ty.return_ty)?)
                    }
                    _ => Err(TcError::UnsupportedTyFnApplication { subject_id: app_ty_fn.subject }),
                }
            }
            Term::TyFnTy(_) => {
                // The type of a type function type is Root
                Ok(self.builder().create_root_term())
            }
            Term::Var(_) => {
                tc_panic!(term_id, self, "Var should have already been simplified away!")
            }
            Term::TyFn(ty_fn) => {
                // The type of a type function is a type function type:
                Ok(self
                    .builder()
                    .create_ty_fn_ty_term(ty_fn.general_params, ty_fn.general_return_ty))
            }
            Term::Merge(terms) => {
                // The type of a merge is a merge of the inner terms:
                let tys_of_terms: Vec<_> = self
                    .reader()
                    .get_term_list_owned(terms)
                    .iter()
                    .map(|term| self.infer_ty_of_term(*term))
                    .collect::<TcResult<_>>()?;

                Ok(self.builder().create_merge_term(tys_of_terms))
            }
            Term::Union(_) => {
                // The type of a union is "SizedTy":
                // @@Future: relax this
                let rt_instantiable_def = self.builder().create_sized_ty_term();
                Ok(rt_instantiable_def)
            }
            Term::SetBound(set_bound) => {
                // Get the type inside the scope, and then apply it again if necessary
                let result = self.scope_manager().enter_scope(set_bound.scope, |this| {
                    this.typer().infer_ty_of_simplified_term(set_bound.term)
                })?;
                self.discoverer().potentially_apply_set_bound_to_term(set_bound.scope, result)
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
                Level2Term::Trt(_) | Level2Term::AnyTy | Level2Term::SizedTy => {
                    Ok(self.builder().create_trt_kind_term())
                }
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
                    // "SizedTy":
                    let rt_instantiable_def = self.builder().create_sized_ty_term();
                    Ok(rt_instantiable_def)
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
                        // The type of an enum variant is the enum, with any data members as
                        // function arguments:
                        //
                        // For an enum variant Foo::Bar(x: A, y: B), we create:
                        // (x: A, y: B) -> Bar
                        let variant = self.oracle().get_enum_variant_info(enum_variant);
                        let enum_ty = self.builder().create_nominal_def_term(enum_variant.def_id);
                        match variant.fields {
                            Some(fields) => Ok(self.builder().create_fn_ty_term(
                                Some(variant.name),
                                fields,
                                enum_ty,
                            )),
                            None => Ok(enum_ty),
                        }
                    }
                    Level0Term::FnCall(_) => {
                        tc_panic!(term_id, self, "Function call should have been simplified away when trying to get the type of the term!")
                    }
                    Level0Term::Tuple(tuple_lit) => {
                        // Get the type of the tuple arguments as parameters:
                        let params = self.infer_params_of_args(tuple_lit.members, false)?;
                        Ok(self.builder().create_tuple_ty_term(params))
                    }
                    Level0Term::Constructed(ConstructedTerm { subject, .. }) => Ok(subject),
                    Level0Term::Lit(lit_term) => {
                        // This gets the type of the literal
                        let term = match lit_term {
                            LitTerm::Str(_) => self.core_defs().str_ty(),
                            // @@Todo: do some more sophisticated inferring here
                            LitTerm::Int { value } => {
                                let kind: Identifier =
                                    CONSTANT_MAP.map_int_constant(value, |int| int.ty()).into();
                                self.core_defs().resolve_core_def(kind)
                            }
                            LitTerm::Char(_) => self.core_defs().char_ty(),
                        };
                        Ok(self.simplifier().potentially_simplify_term(term)?)
                    }
                    Level0Term::Unit(def_id) => {
                        // The inner member stores the def ID of the unit
                        Ok(self.builder().create_nominal_def_term(def_id))
                    }
                }
            }
            Term::BoundVar(bound_var) => {
                // Get its type from the surrounding context:
                // @@Correctness: is there a point here when we should default to typeof()
                // wrapping instead?
                let member = self.scope_manager().get_bound_var_member(bound_var, term_id);
                Ok(member.member.ty())
            }
            Term::ScopeVar(scope_var) => {
                let scope_member = self.scope_manager().get_scope_var_member(scope_var);
                match scope_member.member {
                    Member::Bound(_) => Ok(self.builder().create_ty_of_term(term_id)),
                    Member::Constant(constant) => Ok(constant
                        .if_closed(|_| Some(constant.ty))
                        .unwrap_or_else(|| self.builder().create_ty_of_term(term_id))),
                    Member::SetBound(set_bound) => Ok(set_bound.ty),
                    Member::Variable(variable) => Ok(variable.ty),
                }
            }
            Term::Root | Term::TyOf(_) => {
                // Since these are simplified already, all we can do is wrap it again..
                Ok(self.builder().create_ty_of_term(term_id))
            }
        }?;

        self.location_store().copy_location(term_id, new_term);
        Ok(new_term)
    }

    /// From the given [ArgsId], infer a [ParamsId] describing the the
    /// arguments.
    ///
    /// This will populate the default values with the values of the args if
    /// `populate_defaults` is true.
    pub(crate) fn infer_params_of_args(
        &self,
        args_id: ArgsId,
        populate_defaults: bool,
    ) -> TcResult<ParamsId> {
        self.args_store().map_as_param_list(args_id, |args| {
            let params_list: Vec<_> = args
                .borrowed()
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

            let params_id =
                self.builder().create_params(params_list.iter().copied(), args.origin());

            // Copy locations:
            for i in 0..params_list.len() {
                self.location_store().copy_location((args_id, i), (params_id, i))
            }

            Ok(params_id)
        })
    }

    /// Create an argument from a parameter. This will copy the name
    /// from the parameter and set the value of the argument to the
    /// default value from the parameter.
    ///
    /// *Note*: This expects that the parameter has a default value.
    pub(crate) fn infer_arg_from_param(&self, param: &Param) -> Arg {
        Arg { name: param.name, value: param.default_value.unwrap() }
    }

    /// From the given [ParamsId], infer an [ArgsId] by populating any field
    /// that is present within the parameters and has a default value, into
    /// the args is by being careful not to overwrite the specified
    /// arguments with default values of the parameters.
    pub(crate) fn infer_args_from_params(
        &self,
        args_id: ArgsId,
        params_id: ParamsId,
        params_subject: TermId,
        args_subject: TermId,
    ) -> TcResult<ArgsId> {
        self.params_store().map_as_param_list(params_id, |params| {
            self.args_store().map_as_param_list(args_id, |args| {
                // Pair parameters and arguments, then extract the resultant arguments...
                let pairs = pair_args_with_params(
                    &params,
                    &args,
                    params_id,
                    args_id,
                    |p| self.infer_arg_from_param(p),
                    params_subject,
                    args_subject,
                )?;

                let arg_pairs: Vec<_> = pairs.iter().map(|(_, arg)| *arg.as_ref()).collect();
                let params_sub = self.unifier().unify_param_arg_pairs(pairs)?;

                // Copy over the origin from the initial args
                let new_args = self.builder().create_args(arg_pairs, args.origin());

                // Apply substitution to arguments
                Ok(self.substituter().apply_sub_to_args(&params_sub, new_args))
            })
        })
    }

    /// From the given [PatArgsId], infer a [ArgsId] describing the the
    /// arguments.
    pub(crate) fn infer_args_of_pat_args(&self, id: PatArgsId) -> TcResult<ArgsId> {
        self.pat_args_store().map_as_param_list(id, |pat_args| {
            let arg_tys: Vec<_> = pat_args
                .borrowed()
                .into_positional()
                .into_iter()
                .map(|param| Ok(Arg { name: param.name, value: self.get_term_of_pat(param.pat)? }))
                .collect::<TcResult<_>>()?;

            let args_id = self.builder().create_args(arg_tys.iter().copied(), pat_args.origin());

            // Copy locations:
            for i in 0..arg_tys.len() {
                self.location_store().copy_location((id, i), (args_id, i))
            }

            Ok(args_id)
        })
    }

    /// Get the type of the given pattern, as a term.
    pub(crate) fn infer_ty_of_pat(&self, pat: PatId) -> TcResult<TermId> {
        let pat_term = self.get_term_of_pat(pat)?;
        self.infer_ty_of_term(pat_term)
    }

    /// Get the term of the given pattern, whose type is the type of the pattern
    /// subject.
    pub(crate) fn get_term_of_pat(&self, pat_id: PatId) -> TcResult<TermId> {
        let pat = self.reader().get_pat(pat_id);

        let mut copy_location_to_term = true;

        let ty_of_pat = match pat {
            Pat::Mod(_) | Pat::Wild | Pat::Binding(_) => {
                // We don't know this; it depends on the subject:
                Ok(self.builder().create_unresolved_term())
            }
            Pat::Const(ConstPat { term }) => {
                copy_location_to_term = false;
                Ok(term)
            }
            Pat::Access(AccessPat { subject, property }) => {
                let term = self.get_term_of_pat(subject)?;
                let access_term = self.builder().create_access(term, property, AccessOp::Namespace);
                Ok(self.simplifier().potentially_simplify_term(access_term)?)
            }
            Pat::Lit(lit_term) => Ok(lit_term),
            Pat::Range(RangePat { lo, .. }) => {
                copy_location_to_term = false;

                // The term of the range is the type of `lo` since `lo` is a literal term
                Ok(lo)
            }
            Pat::Tuple(tuple_pat) => {
                // For each parameter, get its type, and then create a tuple
                // type:
                let params_id = self.infer_args_of_pat_args(tuple_pat)?;
                Ok(self.builder().create_tuple_lit_term(params_id))
            }
            Pat::Constructor(constructor_pat) => {
                // We have params to apply, so we need to create an FnCall
                let args_id = self.infer_args_of_pat_args(constructor_pat.args)?;
                Ok(self.builder().create_constructed_term(constructor_pat.subject, args_id))
            }
            Pat::Array(ArrayPat { list_element_ty, .. }) => {
                // @@Future: use a list literal term instead
                //
                // We want to create a `List<T = term>` as the type of the pattern
                let list_inner_ty = self.core_defs().array_ty();
                let builder = self.builder();

                let list_ty = builder.create_app_ty_fn_term(
                    list_inner_ty,
                    builder
                        .create_args([builder.create_arg("T", list_element_ty)], ParamOrigin::TyFn),
                );

                Ok(builder.create_rt_term(list_ty))
            }
            Pat::Spread(_) => {
                let list_inner_ty = self.core_defs().array_ty();
                let builder = self.builder();

                // Since we don't know what the type of the inner term... we leave it as
                // unresolved for later, it will be resolved during further inference
                let unknown_term = builder.create_unresolved_term();

                let list_ty = builder.create_app_ty_fn_term(
                    list_inner_ty,
                    builder.create_args(
                        [builder.create_nameless_arg(unknown_term)],
                        ParamOrigin::TyFn,
                    ),
                );

                Ok(builder.create_rt_term(list_ty))
            }
            Pat::Or(pats) => {
                // Get the inner pattern types:
                let pat_tys: Vec<_> = pats
                    .into_iter()
                    .map(|pat| self.infer_ty_of_pat(pat))
                    .collect::<TcResult<_>>()?;
                // Create a union type:
                let builder = self.builder();
                Ok(builder.create_rt_term(builder.create_union_term(pat_tys)))
            }
            Pat::If(if_pat) => {
                // Forward to the pattern
                self.get_term_of_pat(if_pat.pat)
            }
        }?;

        // Only copy the location if we are creating a new term, not taking one
        // that exists as to avoid overriding it.
        if copy_location_to_term {
            self.location_store().copy_location(pat_id, ty_of_pat);
        }

        Ok(ty_of_pat)
    }

    /// Get the parameters of the given tuple term, if possible.
    ///
    /// This function returns [Some(..)] if the term is validated and
    /// simplified, and is a tuple term (either literal or Rt.). Otherwise
    /// it will return None.
    ///
    /// This function will populate default values if it can (if the tuple is a
    /// literal).
    pub(crate) fn infer_params_ty_of_tuple_term(
        &self,
        tuple_term_id: TermId,
    ) -> TcResult<Option<ParamsId>> {
        // First, try to read the value as a tuple literal:
        let tuple_term = self.reader().get_term(tuple_term_id);
        match tuple_term {
            Term::Level0(Level0Term::Tuple(tuple_lit)) => {
                Ok(Some(self.infer_params_of_args(tuple_lit.members, true)?))
            }
            _ => {
                let tuple_ty_id = self.infer_ty_of_simplified_term(tuple_term_id)?;

                // Otherwise, get the type and try to get the parameters that way:
                let tuple_ty = self.reader().get_term(tuple_ty_id);
                match tuple_ty {
                    Term::Merge(terms) => {
                        // Try each term:
                        self.reader()
                            .get_term_list_owned(terms)
                            .into_iter()
                            .map(|term| self.infer_params_ty_of_tuple_term(term))
                            .flatten_ok()
                            .next()
                            .transpose()
                    }
                    // @@Todo: remove default members:
                    Term::Level1(Level1Term::Tuple(tuple_ty)) => Ok(Some(tuple_ty.members)),
                    _ => Ok(None),
                }
            }
        }
    }

    /// Get the parameters and subject of the given nominal term, if possible.
    ///
    /// This function returns a list of constructors for the given nominal term,
    /// as pairs of function call subject and params. If the list is empty,
    /// there are no constructors.
    ///
    /// This function will populate default values in the params if it can (if
    /// the term is a constructed literal).
    ///
    /// Note: Assumes the term is simplified.
    pub(crate) fn infer_constructor_of_nominal_term(
        &self,
        term: TermId,
    ) -> TcResult<Vec<(TermId, ParamsId)>> {
        match self.reader().get_term(term) {
            Term::Level0(Level0Term::Constructed(ConstructedTerm { subject, members })) => {
                let members = self.infer_params_of_args(members, true)?;
                Ok(vec![(subject, members)])
            }
            Term::Level1(Level1Term::NominalDef(nominal_id)) => {
                match self.reader().get_nominal_def(nominal_id) {
                    NominalDef::Struct(struct_def) => match struct_def.fields {
                        StructFields::Explicit(params) => Ok(vec![(term, params)]),
                        StructFields::Opaque => Ok(vec![]),
                    },
                    _ => Ok(vec![]),
                }
            }
            _ => {
                let constructed_ty_id = self.infer_ty_of_simplified_term(term)?;

                match self.reader().get_term(constructed_ty_id) {
                    Term::Union(terms) => {
                        // Accumulate all terms
                        self.reader()
                            .get_term_list_owned(terms)
                            .into_iter()
                            .map(|term| self.infer_constructor_of_nominal_term(term))
                            .flatten_ok()
                            .collect()
                    }
                    Term::SetBound(set_bound) => {
                        // Recurse to inner and then apply the set bound on the results
                        let result = self.scope_manager().enter_scope(set_bound.scope, |this| {
                            this.typer().infer_constructor_of_nominal_term(set_bound.term)
                        })?;
                        result
                            .into_iter()
                            .map(|(term, params)| {
                                Ok((
                                    self.discoverer().potentially_apply_set_bound_to_term(
                                        set_bound.scope,
                                        term,
                                    )?,
                                    self.discoverer()
                                        .apply_set_bound_to_params(set_bound.scope, params)?,
                                ))
                            })
                            .collect()
                    }
                    Term::Merge(terms) => {
                        // Try each term:
                        self.reader()
                            .get_term_list_owned(terms)
                            .into_iter()
                            .map(|term| self.infer_constructor_of_nominal_term(term))
                            .flatten_ok()
                            .collect()
                    }
                    Term::Level1(Level1Term::NominalDef(nominal_id)) => {
                        match self.reader().get_nominal_def(nominal_id) {
                            NominalDef::Struct(struct_def) => match struct_def.fields {
                                // @@Todo: remove default members:
                                StructFields::Explicit(params) => Ok(vec![(term, params)]),
                                StructFields::Opaque => Ok(vec![]),
                            },
                            _ => Ok(vec![]),
                        }
                    }
                    _ => Ok(vec![]),
                }
            }
        }
    }
}
