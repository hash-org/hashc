//! Operations to infer types of terms and patterns.

use derive_more::{Constructor, Deref};
use hash_ast::ast::{FloatLitKind, IntLitKind};
use hash_intrinsics::utils::PrimitiveUtils;
use hash_source::constant::{FloatTy, IntTy, SIntTy, UIntTy};
use hash_tir::{
    new::{
        args::{ArgsId, PatArgsId},
        casting::CastTerm,
        control::{LoopControlTerm, LoopTerm, ReturnTerm},
        data::{
            CtorDefId, CtorTerm, DataDefCtors, DataDefId, DataTy, ListCtorInfo, PrimitiveCtorInfo,
        },
        defs::{DefArgsId, DefParamGroup, DefParamGroupData, DefParamsId, DefPatArgsId},
        environment::context::{BindingKind, BoundVarOrigin, ScopeKind},
        fns::{FnBody, FnCallTerm, FnDefId},
        holes::HoleBinderKind,
        lits::{Lit, PrimTerm},
        mods::{ModDefId, ModMemberId, ModMemberValue},
        params::{Param, ParamData, ParamsId},
        pats::{Pat, PatId},
        refs::{DerefTerm, RefTerm, RefTy},
        scopes::{BlockTerm, DeclTerm},
        symbols::Symbol,
        terms::{RuntimeTerm, Term, TermId, UnsafeTerm},
        tuples::{TupleTerm, TupleTy},
        tys::{Ty, TyId, TypeOfTerm},
        utils::{common::CommonUtils, AccessToUtils},
    },
    ty_as_variant,
};
use hash_utils::store::{CloneStore, SequenceStore, SequenceStoreKey, Store};

use super::unification::Uni;
use crate::{
    errors::{TcError, TcResult},
    AccessToTypechecking,
};

#[derive(Constructor, Deref)]
pub struct InferenceOps<'a, T: AccessToTypechecking>(&'a T);

impl<T: AccessToTypechecking> InferenceOps<'_, T> {
    /// Infer the given generic definition arguments (specialised for args and
    /// pat args below)
    pub fn infer_some_def_args<DefArgGroup>(
        &self,
        def_args: &[DefArgGroup],
        annotation_def_params: Option<DefParamsId>,
        infer_def_arg_group: impl Fn(
            &DefArgGroup,
            Option<&DefParamGroup>,
        ) -> TcResult<DefParamGroupData>,
    ) -> TcResult<DefParamsId> {
        // @@Todo: dependent definition parameters
        let mut def_params = vec![];
        let mut error_state = self.new_error_state();

        let mut push_param_group =
            |arg_group: &DefArgGroup, param_group: Option<&DefParamGroup>| {
                if let Some(group) =
                    error_state.try_or_add_error(infer_def_arg_group(arg_group, param_group))
                {
                    def_params.push(group)
                }
            };

        match annotation_def_params {
            Some(annotation_def_params) => {
                self.map_def_params(annotation_def_params, |annotation_def_params| {
                    for (group, annotation_group) in def_args.iter().zip(annotation_def_params) {
                        push_param_group(group, Some(annotation_group));
                    }
                })
            }
            None => {
                for group in def_args {
                    push_param_group(group, None);
                }
            }
        }

        self.return_or_register_errors(
            || Ok(self.param_utils().create_def_params(def_params.into_iter())),
            error_state,
        )
    }

    /// Infer the given definition arguments.
    pub fn infer_def_args(
        &self,
        def_args: DefArgsId,
        annotation_def_params: Option<DefParamsId>,
    ) -> TcResult<(DefArgsId, DefParamsId)> {
        Ok((
            def_args,
            self.stores().def_args().map(def_args, |def_args| {
                self.infer_some_def_args(
                    def_args,
                    annotation_def_params,
                    |def_arg_group, def_param_group| {
                        Ok(DefParamGroupData {
                            implicit: def_arg_group.implicit,
                            params: self
                                .infer_args(
                                    def_arg_group.args,
                                    def_param_group.map(|group| group.params),
                                )?
                                .1,
                        })
                    },
                )
            })?,
        ))
    }

    /// Infer the given definition pattern arguments.
    pub fn infer_def_pat_args(
        &self,
        def_pat_args: DefPatArgsId,
        annotation_def_params: Option<DefParamsId>,
    ) -> TcResult<(DefPatArgsId, DefParamsId)> {
        Ok((
            def_pat_args,
            self.stores().def_pat_args().map(def_pat_args, |def_pat_args| {
                self.infer_some_def_args(
                    def_pat_args,
                    annotation_def_params,
                    |def_pat_arg_group, def_param_group| {
                        Ok(DefParamGroupData {
                            implicit: def_pat_arg_group.implicit,
                            params: self
                                .infer_pat_args(
                                    def_pat_arg_group.pat_args,
                                    def_param_group.map(|group| group.params),
                                )?
                                .1,
                        })
                    },
                )
            })?,
        ))
    }

    /// Infer the given generic arguments (specialised
    /// for args and pat args below).
    pub fn infer_some_args<Arg>(
        &self,
        args: &[Arg],
        annotation_params: Option<ParamsId>,
        infer_arg_ty: impl Fn(&Arg, Option<&Param>) -> TcResult<TyId>,
        get_arg_name: impl Fn(&Arg) -> Symbol,
    ) -> TcResult<ParamsId> {
        // @@Enhancement: param names

        let mut params = vec![];
        let mut error_state = self.new_error_state();

        let mut push_param = |arg: &Arg, param: Option<&Param>| {
            // Infer the type of the argument
            let ty = match error_state.try_or_add_error(infer_arg_ty(arg, param)) {
                // Type was inferred
                Some(ty) => ty,
                // Error or blocking occurred
                None => self.new_ty_hole(),
            };

            // Add the parameter
            params.push(ParamData { name: get_arg_name(arg), ty })
        };

        match annotation_params {
            Some(annotation_params) => self.map_params(annotation_params, |annotation_params| {
                for (arg, param) in args.iter().zip(annotation_params.iter()) {
                    push_param(arg, Some(param))
                }
            }),
            None => {
                for arg in args {
                    push_param(arg, None)
                }
            }
        }
        self.return_or_register_errors(
            || Ok(self.param_utils().create_params(params.into_iter())),
            error_state,
        )
    }

    /// Infer the given arguments, producing inferred parameters.
    pub fn infer_args(
        &self,
        args: ArgsId,
        annotation_params: Option<ParamsId>,
    ) -> TcResult<(ArgsId, ParamsId)> {
        Ok((
            args,
            self.stores().args().map(args, |args| {
                self.infer_some_args(
                    args,
                    annotation_params,
                    |arg, param| Ok(self.infer_term(arg.value, param.map(|param| param.ty))?.1),
                    |arg| self.new_symbol_from_param_index(arg.target),
                )
            })?,
        ))
    }

    /// Infer the given pattern arguments, producing inferred parameters.
    pub fn infer_pat_args(
        &self,
        pat_args: PatArgsId,
        annotation_params: Option<ParamsId>,
    ) -> TcResult<(PatArgsId, ParamsId)> {
        Ok((
            pat_args,
            self.stores().pat_args().map(pat_args, |pat_args| {
                self.infer_some_args(
                    pat_args,
                    annotation_params,
                    |pat_arg, param| {
                        Ok(self.infer_pat(pat_arg.pat, param.map(|param| param.ty))?.1)
                    },
                    |pat_arg| self.new_symbol_from_param_index(pat_arg.target),
                )
            })?,
        ))
    }

    /// Infer the type of a sequence of terms which should all match.
    pub fn infer_unified_list<U: Copy>(
        &self,
        items: &[U],
        infer_item: impl Fn(U) -> TcResult<TyId>,
    ) -> TcResult<TyId> {
        let mut current_ty = self.new_ty_hole();
        let mut error_state = self.new_error_state();

        for term in items {
            match infer_item(*term) {
                Ok(ty) => {
                    match self.unification_ops().unify_tys(ty, current_ty) {
                        Ok(Uni { sub }) => {
                            // Unification succeeded
                            self.substitution_ops().apply_sub_to_ty_in_place(current_ty, &sub);
                        }
                        Err(err @ TcError::Blocked) => {
                            error_state.add_error(err);
                        }
                        Err(err) => {
                            // Error in unification, try to unify the other way
                            match self.unification_ops().unify_tys(current_ty, ty) {
                                Ok(Uni { sub }) => {
                                    // Unification succeeded the other way, so use this
                                    // type as a target
                                    current_ty = ty;
                                    self.substitution_ops()
                                        .apply_sub_to_ty_in_place(current_ty, &sub);
                                }
                                Err(_) => {
                                    // Unification blocked or failed, so we just add the error
                                    error_state.add_error(err);
                                }
                            }
                        }
                    }
                }
                Err(err) => {
                    error_state.add_error(err);
                }
            }
        }

        self.return_or_register_errors(|| Ok(current_ty), error_state)
    }

    /// Infer the given parameters.
    pub fn infer_params(&self, params: ParamsId) -> TcResult<ParamsId> {
        let mut error_state = self.new_error_state();
        self.stores().params().map(params, |params| {
            for param in params {
                let _ = error_state.try_or_add_error(self.infer_ty(param.ty, None));
            }
        });
        self.return_or_register_errors(|| Ok(params), error_state)
    }

    /// Infer the given definition parameters.
    pub fn infer_def_params(&self, def_params_id: DefParamsId) -> TcResult<DefParamsId> {
        self.stores().def_params().map(def_params_id, |def_params| {
            self.infer_some_def_args(def_params, None, |def_params, _| {
                Ok(DefParamGroupData {
                    implicit: def_params.implicit,
                    params: self.infer_params(def_params.params)?,
                })
            })
        })
    }

    /// Infer the type of a runtime term.
    pub fn infer_runtime_term(
        &self,
        term: &RuntimeTerm,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(RuntimeTerm, TyId)> {
        Ok((*term, self.check_by_unify(term.term_ty, annotation_ty)?))
    }

    /// Given an inferred type, and an optional annotation type, unify the two,
    /// and if the result is successful then apply the substitution to the
    /// annotation type and return it (or to the inferred type if the annotation
    /// type is not given). If the unification is blocked then return
    /// TcError::Blocked.
    ///
    /// This is a naive kind of checking which does not take into account the
    /// widening that infer performs. Insufficient for control structures.
    pub fn check_by_unify(&self, inferred_ty: TyId, annotation_ty: Option<TyId>) -> TcResult<TyId> {
        match annotation_ty {
            Some(annotation_ty) => {
                let Uni { sub } = self.unification_ops().unify_tys(inferred_ty, annotation_ty)?;
                self.substitution_ops().apply_sub_to_ty_in_place(annotation_ty, &sub);
                Ok(annotation_ty)
            }
            None => Ok(inferred_ty),
        }
    }

    /// Infer the type of a tuple term.
    pub fn infer_tuple_term(
        &self,
        term: &TupleTerm,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(TupleTerm, TupleTy)> {
        // For now, simple infer and unify is sufficient for tuples
        let inferred_ty = self.new_ty(TupleTy { data: self.infer_args(term.data, None)?.1 });
        Ok((
            *term,
            self.check_by_unify(inferred_ty, annotation_ty)
                .map(|ty| ty_as_variant!(self, self.get_ty(ty), Tuple))?,
        ))
    }

    /// Infer the type of a literal.
    pub fn infer_lit(&self, lit: &Lit, annotation_ty: Option<TyId>) -> TcResult<(Lit, TyId)> {
        // @@Todo: look at annotation for more guidance
        let inferred_ty = self.new_data_ty(match lit {
            Lit::Int(int_lit) => match int_lit.underlying.kind {
                IntLitKind::Suffixed(suffix) => match suffix {
                    IntTy::Int(s_int_ty) => match s_int_ty {
                        SIntTy::I8 => self.primitives().i8(),
                        SIntTy::I16 => self.primitives().i16(),
                        SIntTy::I32 => self.primitives().i32(),
                        SIntTy::I64 => self.primitives().i64(),
                        SIntTy::I128 => self.primitives().i128(),
                        SIntTy::ISize => self.primitives().isize(),
                        SIntTy::IBig => self.primitives().ibig(),
                    },
                    IntTy::UInt(u_int_ty) => match u_int_ty {
                        UIntTy::U8 => self.primitives().u8(),
                        UIntTy::U16 => self.primitives().u16(),
                        UIntTy::U32 => self.primitives().u32(),
                        UIntTy::U64 => self.primitives().u64(),
                        UIntTy::U128 => self.primitives().u128(),
                        UIntTy::USize => self.primitives().usize(),
                        UIntTy::UBig => self.primitives().ubig(),
                    },
                },
                // By default, we assume that all integers are i32 unless annotated otherwise.
                IntLitKind::Unsuffixed => self.primitives().i32(),
            },
            Lit::Str(_) => self.primitives().str(),
            Lit::Char(_) => self.primitives().char(),
            Lit::Float(float) => match float.underlying.kind {
                FloatLitKind::Suffixed(float_suffix) => match float_suffix {
                    FloatTy::F32 => self.primitives().f32(),
                    FloatTy::F64 => self.primitives().f64(),
                },
                // By default, we assume that all floats are f32 unless annotated otherwise.
                FloatLitKind::Unsuffixed => self.primitives().f32(),
            },
        });

        Ok((*lit, self.check_by_unify(inferred_ty, annotation_ty)?))
    }

    /// Infer the type of a primitive term.
    pub fn infer_prim_term(
        &self,
        term: &PrimTerm,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(PrimTerm, TyId)> {
        match term {
            PrimTerm::Lit(lit_term) => Ok((*term, self.infer_lit(lit_term, annotation_ty)?.1)),
            PrimTerm::List(list_term) => {
                let list_inner_type =
                    self.stores().term_list().map_fast(list_term.elements, |elements| {
                        self.infer_unified_list(elements, |term| Ok(self.infer_term(term, None)?.1))
                    })?;
                let list_ty = self.new_ty(DataTy {
                    data_def: self.primitives().list(),
                    args: self.param_utils().create_positional_args_for_data_def(
                        self.primitives().list(),
                        [[self.new_term(Term::Ty(list_inner_type))]],
                    ),
                });
                Ok((*term, list_ty))
            }
        }
    }

    /// Infer the type of a constructor term.
    pub fn infer_ctor_term(
        &self,
        term: &CtorTerm,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(CtorTerm, TyId)> {
        let data_def =
            self.stores().ctor_defs().map_fast(term.ctor.0, |terms| terms[term.ctor.1].data_def_id);
        let _inferred_data_args = self.infer_def_args(term.data_args, None)?; // @@Todo: data def params as annotations
        let _inferred_ctor_args = self.infer_def_args(term.ctor_args, None)?; // @@Todo: data def params as annotations
        let inferred_ty = self.new_ty(DataTy { data_def, args: term.data_args });

        Ok((*term, self.check_by_unify(inferred_ty, annotation_ty)?))
    }

    /// Infer the type of a function call.
    pub fn infer_fn_call_term(
        &self,
        fn_call_term: &FnCallTerm,
        original_term_id: TermId,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(FnCallTerm, TyId)> {
        // @@Todo: annotation
        let subject_ty = self.infer_term(fn_call_term.subject, None)?.1;
        let inferred = self.map_ty(subject_ty, |subject| match subject {
            Ty::Eval(term) => match self.use_term_as_ty(*term) {
                Some(ty) => {
                    // Try the same thing, but with the evaluated type.
                    let new_subject = self.new_term(Term::Ty(ty));
                    self.infer_fn_call_term(
                        &FnCallTerm { subject: new_subject, ..*fn_call_term },
                        original_term_id,
                        annotation_ty,
                    )
                }
                None => Err(TcError::Blocked), // @@Todo: user error?
            },
            Ty::Ref(_) => {
                // Try the same thing, but with the dereferenced type.
                let new_subject =
                    self.new_term(Term::Deref(DerefTerm { subject: fn_call_term.subject }));
                self.infer_fn_call_term(
                    &FnCallTerm { subject: new_subject, ..*fn_call_term },
                    original_term_id,
                    annotation_ty,
                )
                .map_err(|err| {
                    if matches!(err, TcError::NotAFunction { .. }) {
                        // Show it with the reference type:
                        TcError::NotAFunction {
                            fn_call: original_term_id,
                            actual_subject_ty: subject_ty,
                        }
                    } else {
                        err
                    }
                })
            }
            Ty::Fn(fn_ty) => {
                // First infer the parameters of the function call.
                let inferred_fn_call_params = self.infer_args(fn_call_term.args, None)?.1;

                // Unify the parameters of the function call with the parameters of the
                // function type.
                let Uni { sub } =
                    self.unification_ops().unify_params(inferred_fn_call_params, fn_ty.params)?;
                // Apply the substitution to the arguments.
                self.substitution_ops().apply_sub_to_args_in_place(fn_call_term.args, &sub);

                // Create a substitution from the parameters of the function type to the
                // parameters of the function call.
                let arg_sub = self
                    .substitution_ops()
                    .create_sub_from_applying_args_to_params(fn_call_term.args, fn_ty.params)?;

                // Apply the substitution to the return type of the function type.
                Ok((
                    *fn_call_term,
                    self.substitution_ops().apply_sub_to_ty(fn_ty.return_ty, &arg_sub),
                ))
            }
            Ty::Universe(_) | Ty::Data(_) | Ty::Tuple(_) | Ty::Var(_) => {
                // Type variable is not a function type.
                Err(TcError::NotAFunction {
                    fn_call: original_term_id,
                    actual_subject_ty: subject_ty,
                })
            }
            Ty::Hole(_) => Err(TcError::Blocked),
        })?;

        Ok((inferred.0, self.check_by_unify(inferred.1, annotation_ty)?))
    }

    /// Infer the type of a function definition.
    ///
    /// This will infer and modify the type of the function definition, and then
    /// return it.
    pub fn infer_fn_def(&self, fn_def_id: FnDefId, annotation_ty: Option<TyId>) -> TcResult<TyId> {
        let fn_def = self.stores().fn_def().get(fn_def_id);
        self.infer_params(fn_def.ty.params)?;

        match fn_def.body {
            FnBody::Defined(fn_body) => {
                self.context_utils().enter_scope(fn_def_id.into(), || {
                    // @@Todo: `return` statement type inference
                    let inferred_return_ty = self.infer_term(fn_body, None)?.1;

                    // Unify the inferred return type with the declared return type.
                    let Uni { sub } = self
                        .unification_ops()
                        .unify_tys(inferred_return_ty, fn_def.ty.return_ty)?;

                    // Apply the substitution to the function.
                    self.traversing_utils()
                        .visit_fn_def::<!, _>(fn_def_id, &mut |atom| {
                            Ok(self.substitution_ops().apply_sub_to_atom_in_place_once(atom, &sub))
                        })
                        .into_ok();

                    Ok(())
                })?
            }
            FnBody::Intrinsic(_) | FnBody::Axiom => {
                // Do nothing.
            }
        }

        self.check_by_unify(self.new_ty(fn_def.ty), annotation_ty)
    }

    /// Infer the type of a variable, and return it.
    pub fn infer_var(&self, term: Symbol) -> TcResult<TyId> {
        match self.context().get_binding(term).unwrap().kind {
            BindingKind::ModMember(_, _) | BindingKind::Ctor(_, _) => {
                unreachable!("mod members and ctors should have all been resolved by now")
            }
            BindingKind::BoundVar(bound_var) => match bound_var {
                BoundVarOrigin::Fn(fn_def_id, param_index) => Ok(self
                    .stores()
                    .fn_def()
                    .map_fast(fn_def_id, |fn_def| {
                        self.get_param_by_index(fn_def.ty.params, param_index)
                    })
                    .ty),
                BoundVarOrigin::FnTy(fn_ty, param_index) => Ok(self
                    .stores()
                    .ty()
                    .map_fast(fn_ty, |ty| {
                        let fn_ty = ty_as_variant!(self, ty, Fn);
                        self.get_param_by_index(fn_ty.params, param_index)
                    })
                    .ty),
                BoundVarOrigin::Data(data_def_id, def_param_index) => Ok(self
                    .stores()
                    .data_def()
                    .map_fast(data_def_id, |data_def| {
                        self.get_def_param_by_index(data_def.params, def_param_index)
                    })
                    .ty),
                BoundVarOrigin::StackMember(stack_member_id) => Ok(self
                    .stores()
                    .stack()
                    .map_fast(stack_member_id.0, |stack| stack.members[stack_member_id.1].ty)),
                BoundVarOrigin::Hole(_, hole_kind) => match hole_kind {
                    HoleBinderKind::Hole(ty_id) => Ok(ty_id),
                    HoleBinderKind::Guess(term_id, _) => Ok(self.infer_term(term_id, None)?.1), /* @@Todo: unify with guess type? */
                },
            },
        }
    }

    /// Infer the type of a `return` term, and return it.
    pub fn infer_return_term(
        &self,
        return_term: &ReturnTerm,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(ReturnTerm, TyId)> {
        let _ = self.infer_term(return_term.expression, None)?;
        let inferred_ty = self.new_never_ty();
        Ok((*return_term, self.check_by_unify(inferred_ty, annotation_ty)?))
    }

    /// Infer the type of a deref term, and return it.
    pub fn infer_deref_term(
        &self,
        deref_term: &DerefTerm,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(DerefTerm, TyId)> {
        // @@Todo: annotation_ty
        let subject_ty_id = self.infer_term(deref_term.subject, None)?.1;
        let inferred_ty =
            self.stores().ty().map_fast(subject_ty_id, |subject_ty| match subject_ty {
                Ty::Ref(ref_ty) => Ok(ref_ty.ty),
                Ty::Hole(_) => Ok(self.new_ty_hole()),
                _ => Err(TcError::CannotDeref {
                    subject: deref_term.subject,
                    actual_subject_ty: subject_ty_id,
                }),
            })?;

        Ok((*deref_term, self.check_by_unify(inferred_ty, annotation_ty)?))
    }

    /// Infer the type of a type, and return it.
    pub fn infer_ty(&self, ty_id: TyId, annotation_ty: Option<TyId>) -> TcResult<(TyId, TyId)> {
        // @@Todo: cumulative type universe infers, also ensure it is valid in type pos.
        let result = self.stores().ty().map(ty_id, |ty| match ty {
            Ty::Eval(eval) => {
                let eval_inferred = self.infer_term(*eval, annotation_ty)?;
                Ok((self.new_ty(Ty::Eval(eval_inferred.0)), eval_inferred.1))
            }
            Ty::Var(var) => Ok((self.new_ty(*var), self.infer_var(*var)?)),
            Ty::Tuple(tuple_ty) => {
                // Infer the parameters
                self.infer_params(tuple_ty.data)?;

                Ok((ty_id, self.new_small_universe_ty()))
            }
            Ty::Fn(fn_ty) => {
                // @@Todo: purity/unsafe infers

                // Infer the parameters
                self.infer_params(fn_ty.params)?;
                self.context_utils().enter_scope(ScopeKind::FnTy(ty_id), || {
                    // Given the parameters, infer the return type
                    self.infer_ty(fn_ty.return_ty, None)
                })
            }
            Ty::Ref(ref_ty) => {
                // Infer the inner type
                self.infer_ty(ref_ty.ty, None)?;
                Ok((ty_id, self.new_small_universe_ty()))
            }
            Ty::Data(data_ty) => {
                // Infer the arguments.
                let inferred_def_params = self.infer_def_args(data_ty.args, None)?.1;

                // Unified the inferred parameters with the declared parameters.
                let data_ty_params =
                    self.stores().data_def().map_fast(data_ty.data_def, |data_def| data_def.params);
                let Uni { sub } =
                    self.unification_ops().unify_def_params(inferred_def_params, data_ty_params)?;

                // Apply the substitution to the arguments.
                self.substitution_ops().apply_sub_to_def_args_in_place(data_ty.args, &sub);

                Ok((ty_id, self.new_small_universe_ty()))
            }
            Ty::Universe(universe_ty) => Ok((ty_id, self.new_universe_ty(universe_ty.size + 1))),
            Ty::Hole(_) => Err(TcError::Blocked),
        })?;

        Ok((ty_id, self.check_by_unify(result.1, annotation_ty)?))
    }

    /// Infer the type of a loop control term, and return it.
    pub fn infer_loop_control_term(&self, _: &LoopControlTerm) -> TyId {
        // Always `never`.
        self.new_never_ty()
    }

    /// Infer the type of an unsafe term, and return it.
    pub fn infer_unsafe_term(
        &self,
        unsafe_term: &UnsafeTerm,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(UnsafeTerm, TyId)> {
        // @@Todo: unsafe context
        // For now just forward to the inner term.
        Ok((*unsafe_term, self.infer_term(unsafe_term.inner, annotation_ty)?.1))
    }

    /// Infer the type of a loop term, and return it.
    pub fn infer_loop_term(
        &self,
        loop_term: &LoopTerm,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(LoopTerm, TyId)> {
        // Forward to the inner term.
        let _ = self.infer_block_term(&loop_term.block, None)?;
        Ok((*loop_term, self.check_by_unify(self.new_void_ty(), annotation_ty)?))
    }

    /// Infer the type of a block term, and return it.
    pub fn infer_block_term(
        &self,
        block_term: &BlockTerm,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(BlockTerm, TyId)> {
        self.stores().term_list().map_fast(block_term.statements, |statements| {
            self.context_utils().enter_scope(block_term.stack_id.into(), || {
                let mut error_state = self.new_error_state();
                for &statement in statements {
                    let _ = error_state.try_or_add_error(self.infer_term(statement, None));
                }

                // Infer the return value
                let final_ty = error_state
                    .try_or_add_error(self.infer_term(block_term.return_value, annotation_ty));

                Ok((
                    *block_term,
                    self.return_or_register_errors(
                        || self.check_by_unify(final_ty.unwrap().1, annotation_ty),
                        error_state,
                    )?,
                ))
            })
        })
    }

    /// Infer a `typeof` term, and return it.
    pub fn infer_type_of_term(
        &self,
        type_of_term: TypeOfTerm,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(TypeOfTerm, TyId)> {
        let ty_of_term = self.infer_term(type_of_term.term, None)?.1;
        let ty_of_ty = self.infer_ty(ty_of_term, None)?.1;
        Ok((type_of_term, self.check_by_unify(ty_of_ty, annotation_ty)?))
    }

    /// Infer a reference term, and return its type.
    pub fn infer_ref_term(
        &self,
        ref_term: &RefTerm,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(RefTerm, TyId)> {
        let inner_ty = self.infer_term(ref_term.subject, None)?.1;

        Ok((
            *ref_term,
            self.check_by_unify(
                self.new_ty(Ty::Ref(RefTy {
                    ty: inner_ty,
                    mutable: ref_term.mutable,
                    kind: ref_term.kind,
                })),
                annotation_ty,
            )?,
        ))
    }

    /// Infer a cast term, and return its type.
    pub fn infer_cast_term(
        &self,
        cast_term: CastTerm,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(CastTerm, TyId)> {
        let inferred_term_ty = self.infer_term(cast_term.subject_term, None)?.1;
        let Uni { sub } =
            self.unification_ops().unify_tys(inferred_term_ty, cast_term.target_ty)?;
        let subbed_target = self.substitution_ops().apply_sub_to_ty(cast_term.target_ty, &sub);

        Ok((cast_term, self.check_by_unify(subbed_target, annotation_ty)?))
    }

    /// Infer a stack declaration term, and return its type.
    pub fn infer_decl_term(
        &self,
        _decl_term: &DeclTerm,
        _annotation_ty: Option<TyId>,
    ) -> TcResult<(DeclTerm, TyId)> {
        // let uni = self.check_pat(decl_term.bind_pat, decl_term.ty)?;

        todo!()
        // match uni {
        //     Uni::Successful(sub) => {
        //         match decl_term.value {
        //             Some(value) => {
        //                 let new_ty = self.check_term(decl_term.value,
        // ty_id)?;                 todo!()
        //             }
        //             None => {
        //                 todo!()
        //             }
        //         }

        //         self.context_utils().add_decl_term_to_context(&decl_term);
        //     }
        //     Uni::Blocked => {
        //         self.context_utils().add_decl_term_to_context(&decl_term);
        //         Ok(None)
        //     }
        // }
    }

    pub fn generalise_term_inference(&self, inference: (impl Into<Term>, TyId)) -> (TermId, TyId) {
        let (term, ty) = inference;
        let term_id = self.new_term(term);
        (term_id, ty)
    }

    pub fn generalise_term_and_ty_inference(
        &self,
        inference: (impl Into<Term>, impl Into<Ty>),
    ) -> (TermId, TyId) {
        let (term, ty) = inference;
        let term_id = self.new_term(term);
        let ty_id = self.new_ty(ty);
        (term_id, ty_id)
    }

    /// Infer a concrete type for a given term.
    ///
    /// If this is not possible, return `None`.
    /// To create a hole when this is not possible, use
    /// [`InferOps::infer_ty_of_term_or_hole`].
    pub fn infer_term(
        &self,
        term_id: TermId,
        annotation_ty: Option<TyId>,
    ) -> TcResult<(TermId, TyId)> {
        self.stores().term().map(term_id, |term| match term {
            Term::Runtime(rt_term) => self
                .infer_runtime_term(rt_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),
            Term::Tuple(tuple_term) => self
                .infer_tuple_term(tuple_term, annotation_ty)
                .map(|i| self.generalise_term_and_ty_inference(i)),
            Term::Prim(prim_term) => self
                .infer_prim_term(prim_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),
            Term::Ctor(ctor_term) => self
                .infer_ctor_term(ctor_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),
            Term::FnCall(fn_call_term) => self
                .infer_fn_call_term(fn_call_term, term_id, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),
            Term::FnRef(fn_def_id) => Ok((term_id, self.infer_fn_def(*fn_def_id, annotation_ty)?)),
            Term::Var(var_term) => Ok((term_id, self.infer_var(*var_term)?)),
            Term::Return(return_term) => self
                .infer_return_term(return_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),
            Term::Ty(ty_id) => {
                self.infer_ty(*ty_id, annotation_ty).map(|i| self.generalise_term_inference(i))
            }
            Term::Deref(deref_term) => self
                .infer_deref_term(deref_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),
            Term::LoopControl(loop_control_term) => {
                Ok((term_id, self.infer_loop_control_term(loop_control_term)))
            }
            Term::Unsafe(unsafe_term) => self
                .infer_unsafe_term(unsafe_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),

            Term::Loop(loop_term) => self
                .infer_loop_term(loop_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),

            Term::Block(block_term) => self
                .infer_block_term(block_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),

            Term::TypeOf(ty_of_term) => self
                .infer_type_of_term(*ty_of_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),

            Term::Ref(ref_term) => self
                .infer_ref_term(ref_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),

            Term::Cast(cast_term) => self
                .infer_cast_term(*cast_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),

            Term::Decl(decl_term) => self
                .infer_decl_term(decl_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),

            Term::Match(_) => todo!(),
            Term::Assign(_) => todo!(),
            Term::Access(_) => todo!(),
            Term::HoleBinder(_) => todo!(),
            Term::Hole(_) => Err(TcError::Blocked),
        })
    }

    /// Infer the type of a pattern, and return it.
    pub fn infer_pat(&self, pat_id: PatId, annotation_ty: Option<TyId>) -> TcResult<(PatId, TyId)> {
        let pat = self.get_pat(pat_id);

        let inferred_ty = match pat {
            Pat::Binding(binding) => self.infer_var(binding.name)?,
            Pat::Range(range_pat) => {
                let start = self.infer_lit(&range_pat.start.into(), annotation_ty)?.1;
                let end = self.infer_lit(&range_pat.end.into(), annotation_ty)?.1;
                let Uni { sub } = self.unification_ops().unify_tys(start, end)?;
                assert!(sub.is_empty()); // @@Todo: specialised unification for no sub
                self.substitution_ops().apply_sub_to_ty(start, &sub)
            }
            Pat::Lit(lit) => self.infer_lit(&lit.into(), annotation_ty)?.1,
            Pat::Tuple(tuple_pat) => {
                // @@Todo: checking annotations
                let args = self.infer_pat_args(tuple_pat.data, None)?.1;
                self.new_ty(TupleTy { data: args })
            }
            Pat::List(list_term) => {
                // @@Todo: checking annotations
                let list_inner_type =
                    self.stores().pat_list().map_fast(list_term.pats, |elements| {
                        self.infer_unified_list(elements, |pat| Ok(self.infer_pat(pat, None)?.1))
                    })?;

                self.new_ty(DataTy {
                    data_def: self.primitives().list(),
                    args: self.param_utils().create_positional_args_for_data_def(
                        self.primitives().list(),
                        [[self.new_term(Term::Ty(list_inner_type))]],
                    ),
                })
            }
            Pat::Ctor(ctor_pat) => {
                // @@Todo: dependent
                // @@Todo: checking
                let _ = self.infer_def_args(ctor_pat.data_args, None)?;
                let _ = self.infer_def_pat_args(ctor_pat.ctor_pat_args, None)?;
                let data_def = self
                    .stores()
                    .ctor_defs()
                    .map_fast(ctor_pat.ctor.0, |defs| defs[ctor_pat.ctor.1].data_def_id);

                // @@todo: sub args
                self.new_ty(DataTy { data_def, args: ctor_pat.data_args })
            }
            Pat::Or(or_pat) => {
                self.stores().pat_list().map_fast(or_pat.alternatives, |alternatives| {
                    self.infer_unified_list(alternatives, |pat| {
                        Ok(self.infer_pat(pat, annotation_ty)?.1)
                    })
                })?
            }
            Pat::If(if_pat) => {
                let _ = self.infer_term(
                    if_pat.condition,
                    Some(self.new_data_ty(self.primitives().bool())),
                )?;
                self.infer_pat(if_pat.pat, annotation_ty)?.1
            }
        };

        let final_ty = self.check_by_unify(inferred_ty, annotation_ty)?;
        Ok((pat_id, final_ty))
    }

    /// Infer the given constructor definition.
    pub fn infer_ctor_def(&self, ctor: CtorDefId) -> TcResult<()> {
        let (ctor_data_def_id, ctor_params, ctor_result_args) =
            self.stores().ctor_defs().map_fast(ctor.0, |ctors| {
                (ctors[ctor.1].data_def_id, ctors[ctor.1].params, ctors[ctor.1].result_args)
            });

        // Infer the parameters and return type of the data type
        let params = self.infer_def_params(ctor_params)?;
        let return_ty = self.new_ty(DataTy { data_def: ctor_data_def_id, args: ctor_result_args });
        let (return_ty, _) = self.infer_ty(return_ty, None)?;
        let return_ty_args = ty_as_variant!(self, self.get_ty(return_ty), Data).args;

        self.stores().ctor_defs().modify_fast(ctor.0, |ctors| {
            ctors[ctor.1].params = params;
            ctors[ctor.1].result_args = return_ty_args;
        });

        Ok(())
    }

    /// Infer the given data definition.
    pub fn infer_data_def(&self, data_def_id: DataDefId) -> TcResult<()> {
        let (data_def_params, data_def_ctors) = self
            .stores()
            .data_def()
            .map_fast(data_def_id, |data_def| (data_def.params, data_def.ctors));

        let inferred_params = self.infer_def_params(data_def_params)?;

        self.stores().data_def().modify_fast(data_def_id, |def| def.params = inferred_params);

        match data_def_ctors {
            DataDefCtors::Defined(data_def_ctors_id) => {
                let mut error_state = self.new_error_state();

                // Infer each member
                for ctor_idx in data_def_ctors_id.to_index_range() {
                    let _ = error_state
                        .try_or_add_error(self.infer_ctor_def((data_def_ctors_id, ctor_idx)));
                }

                self.return_or_register_errors(|| Ok(()), error_state)
            }
            DataDefCtors::Primitive(primitive) => match primitive {
                PrimitiveCtorInfo::Numeric(_)
                | PrimitiveCtorInfo::Str
                | PrimitiveCtorInfo::Char => {
                    // Nothing to do
                    Ok(())
                }
                PrimitiveCtorInfo::List(list_ctor_info) => {
                    // Infer the inner type
                    let element_ty = self.infer_ty(list_ctor_info.element_ty, None)?.0;
                    self.stores().data_def().modify_fast(data_def_id, |def| {
                        def.ctors =
                            DataDefCtors::Primitive(PrimitiveCtorInfo::List(ListCtorInfo {
                                element_ty,
                            }));
                    });
                    Ok(())
                }
            },
        }
    }

    /// Infer the given module member.
    pub fn infer_mod_member(&self, mod_member: ModMemberId) -> TcResult<()> {
        let value = self
            .stores()
            .mod_members()
            .map_fast(mod_member.0, |members| members[mod_member.1].value);
        match value {
            ModMemberValue::Data(data_def_id) => {
                self.infer_data_def(data_def_id)?;
                Ok(())
            }
            ModMemberValue::Mod(mod_def_id) => {
                self.infer_mod_def(mod_def_id)?;
                Ok(())
            }
            ModMemberValue::Fn(fn_def_id) => {
                self.infer_fn_def(fn_def_id, None)?;
                Ok(())
            }
        }
    }

    /// Infer the given module definition.
    pub fn infer_mod_def(&self, mod_def_id: ModDefId) -> TcResult<()> {
        let members = self.stores().mod_def().map_fast(mod_def_id, |def| def.members);
        let mut error_state = self.new_error_state();

        // Infer each member
        for member_idx in members.to_index_range() {
            let _ = error_state.try_or_add_error(self.infer_mod_member((members, member_idx)));
        }

        self.return_or_register_errors(|| Ok(()), error_state)
    }
}
