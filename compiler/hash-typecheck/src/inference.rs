//! Operations to infer types of terms and patterns.

use derive_more::{Constructor, Deref};
use hash_ast::ast::{FloatLitKind, IntLitKind};
use hash_intrinsics::utils::PrimitiveUtils;
use hash_source::constant::{FloatTy, IntTy, SIntTy, UIntTy};
use hash_tir::{
    new::{
        access::AccessTerm,
        args::{ArgData, ArgId, ArgsId, PatArgData, PatArgsId, PatOrCapture},
        atom_info::ItemInAtomInfo,
        casting::CastTerm,
        control::{IfPat, LoopControlTerm, LoopTerm, OrPat, ReturnTerm},
        data::{
            CtorDefId, CtorPat, CtorTerm, DataDefCtors, DataDefId, DataTy, ListCtorInfo,
            PrimitiveCtorInfo,
        },
        environment::context::{BindingKind, ParamOrigin, ScopeKind},
        fns::{FnBody, FnCallTerm, FnDefId, FnTy},
        lits::{ArrayPat, ListCtor, Lit, PrimTerm},
        locations::LocationTarget,
        mods::{ModDefId, ModMemberId, ModMemberValue},
        params::{Param, ParamData, ParamsId},
        pats::{Pat, PatId, PatListId, RangePat, Spread},
        refs::{DerefTerm, RefTerm, RefTy},
        scopes::{BlockTerm, DeclTerm},
        sub::Sub,
        symbols::Symbol,
        terms::{Term, TermId, TermListId, UnsafeTerm},
        tuples::{TuplePat, TupleTerm, TupleTy},
        tys::{Ty, TyId, TypeOfTerm},
        utils::{common::CommonUtils, AccessToUtils},
    },
    term_as_variant, ty_as_variant,
};
use hash_utils::store::{CloneStore, SequenceStore, SequenceStoreKey, Store};
use itertools::Itertools;

use super::unification::Uni;
use crate::{
    errors::{TcError, TcResult, WrongTermKind},
    AccessToTypechecking,
};

#[derive(Constructor, Deref)]
pub struct InferenceOps<'a, T: AccessToTypechecking>(&'a T);

impl<T: AccessToTypechecking> InferenceOps<'_, T> {
    /// Infer the given generic arguments (specialised
    /// for args and pat args below).
    pub fn infer_some_args<Arg: Clone>(
        &self,
        args: impl Iterator<Item = Arg>,
        annotation_params: ParamsId,
        mut infer_arg: impl FnMut(&Arg, &Param) -> TcResult<(Arg, ParamData)>,
        get_arg_id: impl Fn(usize) -> Option<ArgId>,
        get_arg_value: impl Fn(&Arg) -> Option<TermId>,
    ) -> TcResult<(Vec<Arg>, ParamsId)> {
        let mut collected_args = vec![];
        let mut collected_params = vec![];
        let mut running_sub = Sub::identity();

        let mut error_state = self.new_error_state();

        let mut push_param = |i: usize, arg: Arg, param: &Param| {
            // Apply the running substitution to the parameter
            let subbed_param = Param {
                ty: self.substitution_ops().apply_sub_to_ty(param.ty, &running_sub),
                ..*param
            };

            // Infer the type of the argument
            match error_state.try_or_add_error(infer_arg(&arg, &subbed_param)) {
                // Type was inferred
                Some((inferred_arg, inferred_param)) => {
                    // Extend the running substitution with the new unification result
                    if let Some(arg_value) = get_arg_value(&inferred_arg) {
                        running_sub.insert(param.name, arg_value);
                    }

                    collected_args.push(inferred_arg);

                    // If the original parameter has holes, then we use the
                    // inferred parameter. Otherwise use the original parameter. @@Correctness: do
                    // we need to unify here?
                    if self.substitution_ops().atom_has_holes(param.ty) {
                        collected_params.push(inferred_param);
                    } else {
                        collected_params.push((*param).into());
                    }

                    let applied_param_ty =
                        self.substitution_ops().apply_sub_to_ty(param.ty, &running_sub);

                    running_sub.extend(
                        &self
                            .unification_ops()
                            .unify_tys(inferred_param.ty, applied_param_ty)
                            .unwrap()
                            .sub,
                    );
                }
                // Error occurred
                None => {
                    // Add holes
                    collected_args.push(arg);
                    collected_params.push(ParamData {
                        name: param.name,
                        ty: param.ty,
                        default: param.default,
                    });
                }
            }

            if let Some(arg_id) = get_arg_id(i) {
                self.context_utils().add_arg_binding(arg_id, param.id)
            }
        };

        for (i, (arg, param)) in args.zip(annotation_params.iter()).enumerate() {
            let param = self.stores().params().get_element(param);
            push_param(i, arg, &param)
        }

        self.return_or_register_errors(
            || Ok((collected_args, self.param_utils().create_params(collected_params.into_iter()))),
            error_state,
        )
    }

    /// Infer the type of a sequence of terms which should all match.
    pub fn infer_unified_list<U: Copy>(
        &self,
        items: &[U],
        item_annotation_ty: TyId,
        infer_item: impl Fn(U, TyId) -> TcResult<(U, TyId)>,
        sub_item: impl Fn(U, &Sub) -> U,
    ) -> TcResult<(Vec<U>, TyId)> {
        let mut current_ty = item_annotation_ty;
        let mut error_state = self.new_error_state();
        let mut results = vec![];

        for &item in items {
            match infer_item(item, item_annotation_ty) {
                Ok((inferred_item, ty)) => {
                    match self.unification_ops().unify_tys(ty, current_ty) {
                        Ok(Uni { result, sub, .. }) => {
                            // Unification succeeded
                            current_ty = result;
                            results.push(sub_item(inferred_item, &sub));
                        }
                        Err(err) => {
                            error_state.add_error(err);
                            results.push(inferred_item);
                        }
                    }
                }
                Err(err) => {
                    error_state.add_error(err);
                    results.push(item);
                }
            }
        }

        self.return_or_register_errors(|| Ok((results, current_ty)), error_state)
    }

    /// Infer the given term list as one type.
    ///
    /// Returns the inferred list, and its inferred type.
    pub fn infer_unified_term_list(
        &self,
        term_list_id: TermListId,
        element_annotation_ty: TyId,
    ) -> TcResult<(TermListId, TyId)> {
        let terms = self.stores().term_list().get_vec(term_list_id);
        let (inferred_term_vec, inferred_ty_id) = self.infer_unified_list(
            &terms,
            element_annotation_ty,
            |term, ty| self.infer_term(term, ty),
            |term, sub| self.substitution_ops().apply_sub_to_term(term, sub),
        )?;
        Ok((self.new_term_list(inferred_term_vec), inferred_ty_id))
    }

    /// Infer the given pattern list as one type.
    ///
    /// Returns the inferred list, and its inferred type.
    pub fn infer_unified_pat_list(
        &self,
        pat_list_id: PatListId,
        element_annotation_ty: TyId,
    ) -> TcResult<(PatListId, TyId)> {
        let pats = self.stores().pat_list().get_vec(pat_list_id);
        let (inferred_pat_vec, inferred_ty_id) = self.infer_unified_list(
            &pats,
            element_annotation_ty,
            |pat, ty| match pat {
                PatOrCapture::Pat(pat) => {
                    let (pat, ty) = self.infer_pat(pat, ty)?;
                    Ok((PatOrCapture::Pat(pat), ty))
                }
                PatOrCapture::Capture => Ok((PatOrCapture::Capture, ty)),
            },
            |pat, sub| match pat {
                PatOrCapture::Pat(pat) => {
                    let pat = self.substitution_ops().apply_sub_to_pat(pat, sub);
                    PatOrCapture::Pat(pat)
                }
                PatOrCapture::Capture => PatOrCapture::Capture,
            },
        )?;
        Ok((self.new_pat_list(inferred_pat_vec), inferred_ty_id))
    }

    /// Infer the given arguments, producing inferred parameters.
    pub fn infer_args(
        &self,
        args: ArgsId,
        annotation_params: ParamsId,
    ) -> TcResult<(ArgsId, ParamsId)> {
        self.register_new_atom(args, annotation_params);

        let reordered_args_id =
            self.param_ops().validate_and_reorder_args_against_params(args, annotation_params)?;
        let reordered_args = self.stores().args().map_fast(reordered_args_id, |args| {
            args.iter().map(|arg| ArgData { target: arg.target, value: arg.value }).collect_vec()
        });

        let (inferred_args, inferred_params_id) = self.infer_some_args(
            reordered_args.iter().copied(),
            annotation_params,
            |arg, param| {
                let (term, ty) = self.infer_term(arg.value, param.ty)?;
                Ok((
                    ArgData { target: arg.target, value: term },
                    ParamData { name: param.name, ty, default: param.default },
                ))
            },
            |i| Some((reordered_args_id, i)),
            |arg| Some(arg.value),
        )?;

        let inferred_args_id = self.param_utils().create_args(inferred_args.into_iter());

        self.register_atom_inference(args, inferred_args_id, inferred_params_id);
        Ok((inferred_args_id, inferred_params_id))
    }

    /// Infer the given pattern arguments, producing inferred parameters.
    pub fn infer_pat_args(
        &self,
        pat_args: PatArgsId,
        spread: Option<Spread>,
        annotation_params: ParamsId,
    ) -> TcResult<(PatArgsId, ParamsId)> {
        self.register_new_atom(pat_args, annotation_params);

        self.param_ops().validate_and_reorder_pat_args_against_params(
            pat_args,
            spread,
            annotation_params,
        )?;
        let pat_args_data = self.stores().pat_args().map(pat_args, |pat_args| {
            pat_args
                .iter()
                .map(|pat_arg| PatArgData { target: pat_arg.target, pat: pat_arg.pat })
                .collect_vec()
        });

        let (inferred_pat_args, inferred_params_id) = self.infer_some_args(
            pat_args_data.iter().copied(),
            annotation_params,
            |pat_arg, param| match pat_arg.pat {
                PatOrCapture::Pat(pat) => {
                    let (pat, ty) = self.infer_pat(pat, param.ty)?;
                    Ok((
                        PatArgData {
                            target: self.get_param_index(param.id),
                            pat: PatOrCapture::Pat(pat),
                        },
                        ParamData { name: param.name, ty, default: param.default },
                    ))
                }
                PatOrCapture::Capture => Ok((
                    PatArgData {
                        target: self.get_param_index(param.id),
                        pat: PatOrCapture::Capture,
                    },
                    (*param).into(),
                )),
            },
            |_| None,
            |_| None,
        )?;

        let inferred_pat_args_id =
            self.param_utils().create_pat_args(inferred_pat_args.into_iter());

        self.register_atom_inference(pat_args, inferred_pat_args_id, inferred_params_id);
        Ok((inferred_pat_args_id, inferred_params_id))
    }

    /// Infer the given parameters.
    ///
    /// This modifies the parameters in-place.
    pub fn infer_params(&self, params: ParamsId, origin: ParamOrigin) -> TcResult<ParamsId> {
        // Validate the parameters
        self.param_ops().validate_params(params)?;
        let mut error_state = self.new_error_state();

        for param_id in params.iter() {
            let param = self.stores().params().get_element(param_id);
            if let Some((ty, _)) =
                error_state.try_or_add_error(self.infer_ty(param.ty, self.new_ty_hole()))
            {
                self.stores().params().modify_fast(param_id.0, |params| params[param_id.1].ty = ty);
            }
            self.context_utils().add_param_binding(param_id, origin);
        }

        self.return_or_register_errors(|| Ok(params), error_state)
    }

    /// Given an inferred type, and an optional annotation type, unify the two,
    /// and if the result is successful then apply the substitution to the
    /// annotation type and return it (or to the inferred type if the annotation
    /// type is not given).
    pub fn check_by_unify(&self, inferred_ty: TyId, annotation_ty: TyId) -> TcResult<TyId> {
        let Uni { result, .. } = self.unification_ops().unify_tys(inferred_ty, annotation_ty)?;
        Ok(result)
    }

    /// Check that the given type is well-formed, and normalise it.
    pub fn normalise_and_check_ty(&self, ty: TyId) -> TcResult<TyId> {
        match self.get_ty(ty) {
            Ty::Hole(_) => Ok(ty),
            _ => {
                let (checked_ty, _) = self.infer_ty(ty, self.new_ty_hole())?;
                let norm = self.normalisation_ops();
                let reduced_ty = norm.to_ty(norm.normalise(checked_ty.into())?);
                Ok(reduced_ty)
            }
        }
    }

    /// Infer the type of a tuple term.
    pub fn infer_tuple_term(
        &self,
        term: &TupleTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<(TupleTerm, TupleTy)> {
        let reduced_ty = self.normalise_and_check_ty(annotation_ty)?;
        let params = match self.get_ty(reduced_ty) {
            Ty::Tuple(tuple_ty) => tuple_ty.data,
            Ty::Hole(_) => self.param_utils().create_hole_params_from_args(term.data),
            _ => {
                let inferred = self.param_utils().create_hole_params_from_args(term.data);
                return Err(TcError::MismatchingTypes {
                    expected: reduced_ty,
                    actual: self.new_ty(TupleTy { data: inferred }),
                    inferred_from: Some(original_term_id.into()),
                });
            }
        };

        let (inferred_args, inferred_params) = self.context().enter_scope(
            ScopeKind::TupleTy(TupleTy { data: params }),
            || -> TcResult<_> {
                let args = self.infer_args(term.data, params)?;
                Ok(args)
            },
        )?;

        Ok((TupleTerm { data: inferred_args }, TupleTy { data: inferred_params }))
    }

    /// Infer the type of a literal.
    pub fn infer_lit(&self, lit: &Lit, annotation_ty: TyId) -> TcResult<(Lit, TyId)> {
        let inferred_ty = self.new_data_ty(match lit {
            Lit::Int(int_lit) => {
                match int_lit.underlying.kind {
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
                    _ => {
                        let normalised_annotation_ty =
                            self.normalise_and_check_ty(annotation_ty)?;
                        (match self.get_ty(normalised_annotation_ty) {
                            Ty::Data(data_ty) => match self.get_data_def(data_ty.data_def).ctors {
                                DataDefCtors::Primitive(primitive_ctors) => match primitive_ctors {
                                    PrimitiveCtorInfo::Numeric(numeric) => {
                                        let value = int_lit.value();
                                        // If the value is not compatible with the numeric type,
                                        // then
                                        // return `None` and the unification will fail.
                                        if numeric.is_float
                                            || (!numeric.is_signed && value < 0.into())
                                        {
                                            None
                                        } else {
                                            Some(data_ty.data_def)
                                        }
                                    }
                                    _ => None,
                                },
                                DataDefCtors::Defined(_) => None,
                            },
                            _ => None,
                        })
                        .unwrap_or_else(|| self.primitives().i32())
                    }
                }
            }
            Lit::Str(_) => self.primitives().str(),
            Lit::Char(_) => self.primitives().char(),
            Lit::Float(float_lit) => match float_lit.underlying.kind {
                FloatLitKind::Suffixed(float_suffix) => match float_suffix {
                    FloatTy::F32 => self.primitives().f32(),
                    FloatTy::F64 => self.primitives().f64(),
                },
                FloatLitKind::Unsuffixed => {
                    let normalised_annotation_ty = self.normalise_and_check_ty(annotation_ty)?;
                    (match self.get_ty(normalised_annotation_ty) {
                        Ty::Data(data_ty) => match self.get_data_def(data_ty.data_def).ctors {
                            DataDefCtors::Primitive(primitive_ctors) => match primitive_ctors {
                                PrimitiveCtorInfo::Numeric(numeric) => {
                                    // If the value is not compatible with the numeric type,
                                    // then
                                    // return `None` and the unification will fail.
                                    if !numeric.is_float {
                                        None
                                    } else {
                                        Some(data_ty.data_def)
                                    }
                                }
                                _ => None,
                            },
                            DataDefCtors::Defined(_) => None,
                        },
                        _ => None,
                    })
                    .unwrap_or_else(|| self.primitives().f32())
                }
            },
        });

        Ok((*lit, self.check_by_unify(inferred_ty, annotation_ty)?))
    }

    /// Infer the type of a primitive term.
    pub fn infer_prim_term(
        &self,
        term: &PrimTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<(PrimTerm, TyId)> {
        match term {
            PrimTerm::Lit(lit_term) => Ok((*term, self.infer_lit(lit_term, annotation_ty)?.1)),
            PrimTerm::Array(list_term) => {
                let normalised_ty = self.normalise_and_check_ty(annotation_ty)?;
                let list_annotation_inner_ty = match self.get_ty(normalised_ty) {
                    Ty::Data(data) if data.data_def == self.primitives().list() => {
                        // Type is already checked
                        assert!(data.args.len() == 1);
                        let inner_term = self.stores().args().get_element((data.args, 0)).value;
                        term_as_variant!(self, self.get_term(inner_term), Ty)
                    }
                    Ty::Hole(_) => self.new_ty_hole(),
                    _ => {
                        return Err(TcError::MismatchingTypes {
                            expected: annotation_ty,
                            actual: {
                                self.new_ty(DataTy {
                                    data_def: self.primitives().list(),
                                    args: self.new_args(&[self.new_term(self.new_ty_hole())]),
                                })
                            },
                            inferred_from: Some(original_term_id.into()),
                        })
                    }
                };

                let (inferred_list, inferred_list_inner_ty) =
                    self.infer_unified_term_list(list_term.elements, list_annotation_inner_ty)?;
                let list_ty = self.new_ty(DataTy {
                    data_def: self.primitives().list(),
                    args: self.new_args(&[self.new_term(inferred_list_inner_ty)]),
                });
                Ok((PrimTerm::Array(ListCtor { elements: inferred_list }), list_ty))
            }
        }
    }

    /// Infer the given subject, until it no longer contains any holes.
    pub fn infer_until_no_holes<U: Copy>(
        &self,
        initial: U,
        infer: impl Fn(U) -> TcResult<U>,
        has_holes: impl Fn(U) -> bool,
        location: impl Fn(U) -> LocationTarget,
    ) -> TcResult<U> {
        let mut current = initial;
        const MAX_INFER_ITERATIONS: usize = 5;

        for _ in 0..MAX_INFER_ITERATIONS {
            current = infer(current)?;

            if !has_holes(current) {
                return Ok(current);
            }
        }

        Err(TcError::NeedMoreTypeAnnotationsToInfer { term: location(current) })
    }

    /// Infer a constructor term.
    pub fn infer_ctor_term(
        &self,
        term: &CtorTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<(CtorTerm, DataTy)> {
        let ctor = self.stores().ctor_defs().map_fast(term.ctor.0, |defs| defs[term.ctor.1]);
        let data_def = self.get_data_def(ctor.data_def_id);

        let norm = self.normalisation_ops();
        let reduced_ty = norm.to_ty(norm.normalise(annotation_ty.into())?);

        let annotation_data_ty = match self.get_ty(reduced_ty) {
            Ty::Data(data) if data.data_def == ctor.data_def_id => Some(data),
            Ty::Hole(_) => None,
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: self
                        .new_ty(DataTy { args: term.data_args, data_def: ctor.data_def_id }),
                    inferred_from: Some(original_term_id.into()),
                });
            }
        };

        let term_data_args = if term.data_args.len() == 0 {
            match annotation_data_ty {
                Some(t) => t.args,
                None => self.param_utils().instantiate_params_as_holes(data_def.params),
            }
        } else {
            term.data_args
        };

        let annotation_data_ty =
            annotation_data_ty.unwrap_or(DataTy { args: term_data_args, data_def: data_def.id });

        self.context().enter_scope(data_def.id.into(), || {
            let data_args_uni =
                self.unification_ops().unify_args(term_data_args, annotation_data_ty.args)?;

            // First infer the data arguments
            let (inferred_data_args, inferred_data_params) =
                self.infer_args(data_args_uni.result, data_def.params)?;

            let param_uni = self
                .unification_ops()
                .unify_params(inferred_data_params, data_def.params, ParamOrigin::Ctor(ctor.id))
                .unwrap();

            // Create a substitution from the inferred data arguments
            let data_sub = self
                .substitution_ops()
                .create_sub_from_args_of_params(inferred_data_args, data_def.params);

            self.context().enter_scope(ctor.id.into(), || {
                // Apply the substitution to the constructor parameters
                let subbed_ctor_params = self.substitution_ops().apply_sub_to_params(
                    self.substitution_ops().apply_sub_to_params(
                        self.substitution_ops()
                            .apply_sub_to_params(ctor.params, &data_args_uni.sub),
                        &param_uni.sub,
                    ),
                    &data_sub,
                );

                // Infer the constructor arguments
                let (inferred_ctor_args, inferred_ctor_params) =
                    self.infer_args(term.ctor_args, subbed_ctor_params)?;

                // Create a substitution from the inferred constructor arguments
                let ctor_val_sub = self
                    .substitution_ops()
                    .create_sub_from_args_of_params(inferred_ctor_args, subbed_ctor_params);

                let ctor_ty_sub = self.unification_ops().unify_params(
                    inferred_ctor_params,
                    subbed_ctor_params,
                    ParamOrigin::Ctor(ctor.id),
                )?;
                let ctor_sub = ctor_val_sub.join(&ctor_ty_sub.sub);

                // Apply the substitution to the constructor result args
                let subbed_result_args = self.substitution_ops().apply_sub_to_args(
                    self.substitution_ops().apply_sub_to_args(
                        self.substitution_ops().apply_sub_to_args(ctor.result_args, &param_uni.sub),
                        &data_sub,
                    ),
                    &ctor_sub,
                );

                // Try to unify given annotation with inferred eventual type.
                let result_data_def_args = self
                    .unification_ops()
                    .unify_args(subbed_result_args, inferred_data_args)?
                    .result;

                // Evaluate the result args.
                Ok((
                    CtorTerm {
                        ctor: ctor.id,
                        data_args: result_data_def_args,
                        ctor_args: inferred_ctor_args,
                    },
                    DataTy { args: result_data_def_args, data_def: data_def.id },
                ))
            })
        })
    }

    /// Infer the type of a function call.
    pub fn infer_fn_call_term(
        &self,
        fn_call_term: &FnCallTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<(FnCallTerm, TyId)> {
        let (subject_term, subject_ty) =
            self.infer_term(fn_call_term.subject, self.new_ty_hole())?;
        let normalised_subject_ty = self.normalise_and_check_ty(subject_ty)?;

        match self.get_ty(normalised_subject_ty) {
            Ty::Ref(_) => {
                // Try the same thing, but with the dereferenced type.
                let new_subject = self.new_term(Term::Deref(DerefTerm { subject: subject_term }));
                self.infer_fn_call_term(
                    &FnCallTerm { subject: new_subject, ..*fn_call_term },
                    annotation_ty,
                    original_term_id,
                )
            }
            Ty::Fn(fn_ty) => {
                let infer = || {
                    self.context().enter_scope(ScopeKind::FnTy(fn_ty), || {
                        if fn_ty.implicit != fn_call_term.implicit {
                            return Err(TcError::WrongCallKind {
                                site: original_term_id,
                                expected_implicit: fn_ty.implicit,
                                actual_implicit: fn_call_term.implicit,
                            });
                        }

                        // First infer the arguments parameters of the function call.
                        let (inferred_fn_call_args, inferred_params) =
                            self.infer_args(fn_call_term.args, fn_ty.params)?;

                        let param_uni = self
                            .unification_ops()
                            .unify_params(fn_ty.params, inferred_params, ParamOrigin::FnTy(fn_ty))
                            .unwrap();

                        let sub = self
                            .substitution_ops()
                            .create_sub_from_args_of_params(inferred_fn_call_args, inferred_params);

                        let subbed_return_ty = self.substitution_ops().apply_sub_to_ty(
                            self.substitution_ops()
                                .apply_sub_to_ty(fn_ty.return_ty, &param_uni.sub),
                            &sub,
                        );

                        // Then normalise the return type in their scope.
                        let return_ty = self.normalise_and_check_ty(subbed_return_ty)?;

                        // @@Todo: implicit check
                        let uni = self.unification_ops().unify_tys(return_ty, annotation_ty)?;

                        Ok((
                            FnCallTerm {
                                subject: self.substitution_ops().apply_sub_to_term(
                                    self.substitution_ops()
                                        .apply_sub_to_term(subject_term, &param_uni.sub),
                                    &uni.sub,
                                ),
                                args: inferred_fn_call_args,
                                implicit: fn_call_term.implicit,
                            },
                            uni.result,
                        ))
                    })
                };

                // Potentially fill-in implicit args
                match self.get_ty(fn_ty.return_ty) {
                    Ty::Fn(_) if fn_ty.implicit => infer().or_else(|_| {
                        let applied_args =
                            self.param_utils().instantiate_params_as_holes(fn_ty.params);

                        let new_subject = FnCallTerm {
                            subject: self.new_term(FnCallTerm {
                                args: applied_args,
                                subject: subject_term,
                                implicit: fn_ty.implicit,
                            }),
                            args: fn_call_term.args,
                            implicit: fn_call_term.implicit,
                        };

                        self.infer_fn_call_term(&new_subject, annotation_ty, original_term_id)
                    }),
                    _ => infer(),
                }
            }
            Ty::Hole(_)
            | Ty::Eval(_)
            | Ty::Universe(_)
            | Ty::Data(_)
            | Ty::Tuple(_)
            | Ty::Var(_) => {
                // Not a function type.
                Err(TcError::WrongTy {
                    kind: WrongTermKind::NotAFunction,
                    inferred_term_ty: subject_ty,
                    term: original_term_id,
                })
            }
        }
    }

    /// Infer the type of a function definition.
    ///
    /// This will infer and modify the type of the function definition, and then
    /// return it.
    pub fn infer_fn_def(
        &self,
        fn_def_id: FnDefId,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<FnTy> {
        let fn_def = self.stores().fn_def().get(fn_def_id);

        let annotation_ty = self.normalise_and_check_ty(annotation_ty)?;
        let annotation_fn_ty = match self.get_ty(annotation_ty) {
            Ty::Fn(t) => Some(t),
            Ty::Hole(_) => None,
            _ => {
                return Err(TcError::WrongTy {
                    kind: WrongTermKind::NotAFunction,
                    inferred_term_ty: self.new_ty(fn_def.ty),
                    term: original_term_id,
                })
            }
        };

        match fn_def.body {
            FnBody::Defined(fn_body) => {
                self.context().enter_scope(ScopeKind::Fn(fn_def_id), || {
                    let fn_def = self.stores().fn_def().get(fn_def_id);

                    // Ensure the modalities match if the annotation is given.
                    if let Some(annotation_fn_ty) = annotation_fn_ty {
                        if !self.unification_ops().fn_modalities_match(annotation_fn_ty, fn_def.ty)
                        {
                            return Err(TcError::MismatchingTypes {
                                expected: self.new_ty(annotation_fn_ty),
                                actual: self.new_ty(fn_def.ty),
                                inferred_from: Some(original_term_id.into()),
                            });
                        }
                    }

                    // Ensure that the parameters match
                    let inferred_params_result = if let Some(annotation_fn_ty) = annotation_fn_ty {
                        self.unification_ops().unify_params(
                            annotation_fn_ty.params,
                            fn_def.ty.params,
                            ParamOrigin::Fn(fn_def_id),
                        )?
                    } else {
                        Uni {
                            result: self
                                .infer_params(fn_def.ty.params, ParamOrigin::Fn(fn_def_id))?,
                            sub: Sub::identity(),
                        }
                    };

                    // Ensure that the return types match
                    let (inferred_ret, inferred_ret_ty) =
                        if let Some(annotation_fn_ty) = annotation_fn_ty {
                            let subbed_annotation_ty = self.substitution_ops().apply_sub_to_ty(
                                annotation_fn_ty.return_ty,
                                &inferred_params_result.sub,
                            );

                            let unified_return_ty = self
                                .unification_ops()
                                .unify_tys(fn_def.ty.return_ty, subbed_annotation_ty)?;

                            self.infer_term(fn_body, unified_return_ty.result)?
                        } else {
                            self.infer_term(fn_body, fn_def.ty.return_ty)?
                        };

                    let inferred_fn_ty = FnTy {
                        implicit: fn_def.ty.implicit,
                        is_unsafe: fn_def.ty.is_unsafe,
                        pure: fn_def.ty.pure,

                        params: inferred_params_result.result,
                        return_ty: inferred_ret_ty,
                    };

                    // Modify the fn def
                    self.stores().fn_def().modify_fast(fn_def_id, |def| {
                        def.body = FnBody::Defined(inferred_ret);
                        def.ty = inferred_fn_ty;
                    });

                    Ok(inferred_fn_ty)
                })
            }
            FnBody::Intrinsic(_) | FnBody::Axiom => Ok(fn_def.ty),
        }
    }

    /// Infer the type of a variable, and return it.
    pub fn infer_var(&self, term: Symbol, annotation_ty: TyId) -> TcResult<TyId> {
        let found_ty = match self.context().get_binding(term).kind {
            BindingKind::Equality(_) => {
                unreachable!("equality judgements cannot be referenced")
            }
            BindingKind::ModMember(_, _) | BindingKind::Ctor(_, _) => {
                unreachable!("mod members and ctors should have all been resolved by now")
            }
            BindingKind::Param(_, param_id) => self.stores().params().get_element(param_id).ty,
            BindingKind::StackMember(stack_member_id, _) => self
                .stores()
                .stack()
                .map_fast(stack_member_id.0, |stack| stack.members[stack_member_id.1].ty),
            BindingKind::Arg(param_id, _) => self.stores().params().get_element(param_id).ty,
        };
        self.check_by_unify(found_ty, annotation_ty)
    }

    /// Infer the type of a `return` term, and return it.
    pub fn infer_return_term(
        &self,
        return_term: &ReturnTerm,
        annotation_ty: TyId,
    ) -> TcResult<(ReturnTerm, TyId)> {
        let closest_fn_def_return_ty = self
            .context_utils()
            .get_first_fn_def_in_scope()
            .map(|def| self.stores().fn_def().map_fast(def, |def| def.ty.return_ty))
            .unwrap_or_else(|| self.new_ty_hole());
        let _ = self.infer_term(return_term.expression, closest_fn_def_return_ty)?;

        let inferred_ty = self.new_never_ty();
        Ok((*return_term, self.check_by_unify(inferred_ty, annotation_ty)?))
    }

    /// Infer the type of a deref term, and return it.
    pub fn infer_deref_term(
        &self,
        deref_term: &DerefTerm,
        annotation_ty: TyId,
    ) -> TcResult<(DerefTerm, TyId)> {
        let (subject_term, subject_ty) = self.infer_term(deref_term.subject, self.new_ty_hole())?;

        let inferred_ty = match self.get_ty(subject_ty) {
            Ty::Ref(ref_ty) => ref_ty.ty,
            _ => {
                return Err(TcError::CannotDeref {
                    subject: subject_term,
                    actual_subject_ty: subject_ty,
                })
            }
        };

        Ok((DerefTerm { subject: subject_term }, self.check_by_unify(inferred_ty, annotation_ty)?))
    }

    /// Infer the type of a type, and return it.
    pub fn infer_ty(&self, ty_id: TyId, annotation_ty: TyId) -> TcResult<(TyId, TyId)> {
        self.register_new_atom(ty_id, annotation_ty);

        let result_ty = match self.get_ty(ty_id) {
            Ty::Eval(eval) => {
                let eval_inferred = self.infer_term(eval, annotation_ty)?;
                TcResult::<_>::Ok((self.new_ty(Ty::Eval(eval_inferred.0)), eval_inferred.1))
            }
            Ty::Var(var) => Ok((ty_id, self.infer_var(var, annotation_ty)?)),
            Ty::Tuple(tuple_ty) => {
                // Infer the parameters
                self.infer_params(tuple_ty.data, tuple_ty.into())?;
                Ok((ty_id, self.new_small_universe_ty()))
            }
            Ty::Fn(fn_ty) => {
                // Infer the parameters
                self.context().enter_scope(ScopeKind::FnTy(fn_ty), || {
                    let params = self.infer_params(fn_ty.params, fn_ty.into())?;
                    // Given the parameters, infer the return type
                    let return_ty = self.infer_ty(fn_ty.return_ty, self.new_ty_hole())?;

                    Ok((
                        self.new_ty(Ty::Fn(FnTy {
                            implicit: fn_ty.implicit,
                            is_unsafe: fn_ty.is_unsafe,
                            pure: fn_ty.pure,
                            params,
                            return_ty: return_ty.0,
                        })),
                        self.new_small_universe_ty(),
                    ))
                })
            }
            Ty::Ref(ref_ty) => {
                // Infer the inner type
                let (inner_ty, _) = self.infer_ty(ref_ty.ty, self.new_ty_hole())?;
                Ok((
                    self.new_ty(RefTy { ty: inner_ty, kind: ref_ty.kind, mutable: ref_ty.mutable }),
                    self.new_small_universe_ty(),
                ))
            }
            Ty::Data(data_ty) => {
                self.context().enter_scope(ScopeKind::Data(data_ty.data_def), || {
                    let data_def = self.get_data_def(data_ty.data_def);
                    let (inferred_data_args, _) = self.infer_args(data_ty.args, data_def.params)?;

                    Ok((
                        self.new_ty(Ty::Data(DataTy {
                            args: inferred_data_args,
                            data_def: data_ty.data_def,
                        })),
                        self.new_small_universe_ty(),
                    ))
                })
            }
            Ty::Universe(universe_ty) => Ok((ty_id, self.new_universe_ty(universe_ty.size + 1))),
            Ty::Hole(_) => Ok((ty_id, annotation_ty)),
        }?;

        self.register_atom_inference(ty_id, result_ty.0, result_ty.1);
        Ok((result_ty.0, self.check_by_unify(result_ty.1, annotation_ty)?))
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
        annotation_ty: TyId,
    ) -> TcResult<(UnsafeTerm, TyId)> {
        // @@Todo: unsafe context
        // For now just forward to the inner term.
        Ok((*unsafe_term, self.infer_term(unsafe_term.inner, annotation_ty)?.1))
    }

    /// Infer the type of a loop term, and return it.
    pub fn infer_loop_term(
        &self,
        loop_term: &LoopTerm,
        annotation_ty: TyId,
    ) -> TcResult<(LoopTerm, TyId)> {
        // Forward to the inner term.
        let (inferred_block_term, _) =
            self.infer_block_term(&loop_term.block, self.new_ty_hole())?;
        Ok((
            LoopTerm { block: inferred_block_term },
            self.check_by_unify(self.new_void_ty(), annotation_ty)?,
        ))
    }

    /// Infer the type of a block term, and return it.
    pub fn infer_block_term(
        &self,
        block_term: &BlockTerm,
        annotation_ty: TyId,
    ) -> TcResult<(BlockTerm, TyId)> {
        self.stores().term_list().map(block_term.statements, |statements| {
            self.context().enter_scope(block_term.stack_id.into(), || {
                // Handle local mod def
                let stack = self.stores().stack().get(block_term.stack_id);
                if let Some(local_mod_def) = stack.local_mod_def {
                    self.infer_mod_def(local_mod_def)?;
                }

                let mut error_state = self.new_error_state();
                let mut inferred_statements = vec![];
                for &statement in statements {
                    match error_state
                        .try_or_add_error(self.infer_term(statement, self.new_ty_hole()))
                    {
                        Some((inferred_statement, _)) => {
                            inferred_statements.push(inferred_statement);
                        }
                        None => {
                            inferred_statements.push(statement);
                        }
                    }
                }

                // Infer the return value
                let (return_term, subbed_return_ty) = match error_state
                    .try_or_add_error(self.infer_term(block_term.return_value, annotation_ty))
                {
                    Some((return_term, return_ty)) => {
                        let sub = self.substitution_ops().create_sub_from_current_stack_members();
                        (return_term, self.substitution_ops().apply_sub_to_ty(return_ty, &sub))
                    }
                    None => (block_term.return_value, annotation_ty),
                };

                self.return_or_register_errors(
                    || {
                        Ok((
                            BlockTerm {
                                statements: self.new_term_list(inferred_statements),
                                return_value: return_term,
                                stack_id: block_term.stack_id,
                            },
                            subbed_return_ty,
                        ))
                    },
                    error_state,
                )
            })
        })
    }

    /// Infer a `typeof` term, and return it.
    pub fn infer_type_of_term(
        &self,
        type_of_term: TypeOfTerm,
        annotation_ty: TyId,
    ) -> TcResult<(TypeOfTerm, TyId)> {
        let (inferred_term, inferred_ty) =
            self.infer_term(type_of_term.term, self.new_ty_hole())?;
        let (_, inferred_ty_of_ty) = self.infer_ty(inferred_ty, annotation_ty)?;
        Ok((TypeOfTerm { term: inferred_term }, inferred_ty_of_ty))
    }

    /// Infer a reference term, and return its type.
    pub fn infer_ref_term(
        &self,
        ref_term: &RefTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<(RefTerm, RefTy)> {
        let normalised_ty = self.normalise_and_check_ty(annotation_ty)?;
        let annotation_ref_ty = match self.get_ty(normalised_ty) {
            Ty::Ref(ref_ty) => ref_ty,
            Ty::Hole(_) => {
                RefTy { kind: ref_term.kind, mutable: ref_term.mutable, ty: self.new_ty_hole() }
            }
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: self.new_ty(RefTy {
                        kind: ref_term.kind,
                        mutable: ref_term.mutable,
                        ty: self.new_ty_hole(),
                    }),
                    inferred_from: Some(original_term_id.into()),
                })
            }
        };

        let (inner_term, inner_ty) = self.infer_term(ref_term.subject, annotation_ref_ty.ty)?;

        Ok((
            RefTerm { subject: inner_term, ..*ref_term },
            RefTy { ty: inner_ty, ..annotation_ref_ty },
        ))
    }

    /// Infer a cast term, and return its type.
    pub fn infer_cast_term(
        &self,
        cast_term: CastTerm,
        annotation_ty: TyId,
    ) -> TcResult<(CastTerm, TyId)> {
        let (inferred_term, inferred_term_ty) =
            self.infer_term(cast_term.subject_term, cast_term.target_ty)?;
        let Uni { sub, .. } = self.unification_ops().unify_tys(inferred_term_ty, annotation_ty)?;
        let subbed_ty = self.substitution_ops().apply_sub_to_ty(inferred_term_ty, &sub);
        let subbed_term = self.substitution_ops().apply_sub_to_term(inferred_term, &sub);

        Ok((CastTerm { subject_term: subbed_term, target_ty: subbed_ty }, inferred_term_ty))
    }

    /// Infer a stack declaration term, and return its type.
    pub fn infer_decl_term(
        &self,
        decl_term: &DeclTerm,
        annotation_ty: TyId,
    ) -> TcResult<(DeclTerm, TyId)> {
        let result_decl_term: TcResult<DeclTerm> = try {
            let decl_term_ty = self.normalise_and_check_ty(decl_term.ty)?;

            let (inferred_rhs_value, inferred_ty) = match decl_term.value {
                Some(value) => {
                    let (inferred_value, inferred_ty) = self.infer_term(value, decl_term_ty)?;
                    (Some(inferred_value), inferred_ty)
                }
                None => (None, decl_term_ty),
            };

            let (inferred_lhs_pat, inferred_ty) =
                self.infer_pat(decl_term.bind_pat, inferred_ty)?;

            let result_decl_term = DeclTerm {
                bind_pat: inferred_lhs_pat,
                value: inferred_rhs_value,
                ty: inferred_ty,
                stack_indices: decl_term.stack_indices,
            };

            result_decl_term
        };

        match result_decl_term {
            Ok(result_decl_term) => {
                self.context_utils().add_from_decl_term(&result_decl_term);
                Ok((result_decl_term, self.check_by_unify(self.new_void_ty(), annotation_ty)?))
            }
            Err(err) => {
                // We still want to add the bindings from the decl term to the context, even if
                // the term is invalid.
                self.context_utils().add_from_decl_term(decl_term);
                Err(err)
            }
        }
    }

    /// Infer an access term.
    pub fn infer_access_term(
        &self,
        access_term: &AccessTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<(AccessTerm, TyId)> {
        let (inferred_subject, inferred_subject_ty) =
            self.infer_term(access_term.subject, self.new_ty_hole())?;

        let normalised_subject_ty = self.normalise_and_check_ty(inferred_subject_ty)?;

        let params = match self.get_ty(normalised_subject_ty) {
            Ty::Tuple(tuple_ty) => tuple_ty.data,
            Ty::Data(data_ty) => {
                match self.data_utils().get_single_ctor_of_data_def(data_ty.data_def) {
                    Some(ctor) => {
                        let data_def = self.get_data_def(data_ty.data_def);
                        let sub = self
                            .substitution_ops()
                            .create_sub_from_args_of_params(data_ty.args, data_def.params);
                        self.substitution_ops().apply_sub_to_params(ctor.params, &sub)
                    }
                    None => {
                        // Not a record type because it has more than one constructor
                        // @@ErrorReporting: more information about the error
                        return Err(TcError::WrongTy {
                            kind: WrongTermKind::NotARecord,
                            inferred_term_ty: normalised_subject_ty,
                            term: original_term_id,
                        });
                    }
                }
            }

            // Not a record type.
            _ => {
                return Err(TcError::WrongTy {
                    kind: WrongTermKind::NotARecord,
                    inferred_term_ty: normalised_subject_ty,
                    term: original_term_id,
                })
            }
        };

        if let Some(param) = self.try_get_param_by_index(params, access_term.field) {
            // Create a substitution that maps the parameters of the record
            // type to the corresponding fields of the record term.
            //
            // i.e. `x: (T: Type, t: T);  x.t: x.T`
            let param_access_sub =
                self.substitution_ops().create_sub_from_param_access(params, inferred_subject);

            let subbed_param_ty =
                self.substitution_ops().apply_sub_to_ty(param.ty, &param_access_sub);

            let unified_ty = self.check_by_unify(subbed_param_ty, annotation_ty)?;

            Ok((AccessTerm { subject: inferred_subject, field: access_term.field }, unified_ty))
        } else {
            Err(TcError::PropertyNotFound {
                term: inferred_subject,
                term_ty: normalised_subject_ty,
                property: access_term.field,
            })
        }
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

    pub fn generalise_pat_inference(&self, inference: (impl Into<Pat>, TyId)) -> (PatId, TyId) {
        let (term, ty) = inference;
        let term_id = self.new_pat(term);
        (term_id, ty)
    }

    pub fn generalise_pat_and_ty_inference(
        &self,
        inference: (impl Into<Pat>, impl Into<Ty>),
    ) -> (PatId, TyId) {
        let (term, ty) = inference;
        let term_id = self.new_pat(term);
        let ty_id = self.new_ty(ty);
        (term_id, ty_id)
    }

    /// Infer a concrete type for a given term.
    ///
    /// If this is not possible, return `None`.
    /// To create a hole when this is not possible, use
    /// [`InferOps::infer_ty_of_term_or_hole`].
    pub fn infer_term(&self, term_id: TermId, annotation_ty: TyId) -> TcResult<(TermId, TyId)> {
        self.register_new_atom(term_id, annotation_ty);

        let result = self.stores().term().map(term_id, |term| match term {
            Term::Tuple(tuple_term) => self
                .infer_tuple_term(tuple_term, annotation_ty, term_id)
                .map(|i| self.generalise_term_and_ty_inference(i)),
            Term::Prim(prim_term) => self
                .infer_prim_term(prim_term, annotation_ty, term_id)
                .map(|i| self.generalise_term_inference(i)),
            Term::Ctor(ctor_term) => self
                .infer_ctor_term(ctor_term, annotation_ty, term_id)
                .map(|i| self.generalise_term_and_ty_inference(i)),
            Term::FnCall(fn_call_term) => self
                .infer_fn_call_term(fn_call_term, annotation_ty, term_id)
                .map(|i| self.generalise_term_inference(i)),
            Term::FnRef(fn_def_id) => {
                Ok((term_id, self.new_ty(self.infer_fn_def(*fn_def_id, annotation_ty, term_id)?)))
            }
            Term::Var(var_term) => Ok((term_id, self.infer_var(*var_term, annotation_ty)?)),
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
                .infer_ref_term(ref_term, annotation_ty, term_id)
                .map(|i| self.generalise_term_and_ty_inference(i)),

            Term::Cast(cast_term) => self
                .infer_cast_term(*cast_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),

            Term::Decl(decl_term) => self
                .infer_decl_term(decl_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),

            Term::Access(access_term) => self
                .infer_access_term(access_term, annotation_ty, term_id)
                .map(|i| self.generalise_term_inference(i)),

            // @@Todo:
            Term::Match(_) | Term::Assign(_) => {
                // @@Todo
                Ok((term_id, annotation_ty))
            }

            Term::Hole(_) => Ok((term_id, annotation_ty)),
        })?;

        self.register_atom_inference(term_id, result.0, result.1);
        Ok(result)
    }

    /// Infer a range pattern.
    pub fn infer_range_pat(&self, range_pat: RangePat, annotation_ty: TyId) -> TcResult<TyId> {
        let (_, start_ty) = self.infer_lit(&range_pat.start.into(), annotation_ty)?;
        let (_, end_ty) = self.infer_lit(&range_pat.end.into(), annotation_ty)?;

        let Uni { sub, result } = self.unification_ops().unify_tys(start_ty, end_ty)?;
        assert!(sub.is_empty()); // @@Todo: specialised unification for no sub
        Ok(result)
    }

    /// Infer a tuple pattern.
    pub fn infer_tuple_pat(
        &self,
        tuple_pat: &TuplePat,
        annotation_ty: TyId,
        original_pat_id: PatId,
    ) -> TcResult<(TuplePat, TupleTy)> {
        let reduced_ty = self.normalise_and_check_ty(annotation_ty)?;
        let params = match self.get_ty(reduced_ty) {
            Ty::Tuple(tuple_ty) => tuple_ty.data,
            Ty::Hole(_) => self.param_utils().create_hole_params_from_args(tuple_pat.data),
            _ => {
                let inferred = self.param_utils().create_hole_params_from_args(tuple_pat.data);
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: self.new_ty(TupleTy { data: inferred }),
                    inferred_from: Some(original_pat_id.into()),
                });
            }
        };

        let (inferred_args, inferred_params) =
            self.context().enter_scope(ScopeKind::TupleTy(TupleTy { data: params }), || {
                self.infer_pat_args(tuple_pat.data, tuple_pat.data_spread, params)
            })?;

        Ok((
            TuplePat { data: inferred_args, data_spread: tuple_pat.data_spread },
            TupleTy { data: inferred_params },
        ))
    }

    /// Infer a list pattern
    pub fn infer_list_pat(
        &self,
        list_pat: &ArrayPat,
        annotation_ty: TyId,
        original_pat_id: PatId,
    ) -> TcResult<(ArrayPat, DataTy)> {
        let normalised_ty = self.normalise_and_check_ty(annotation_ty)?;
        let list_annotation_inner_ty = match self.get_ty(normalised_ty) {
            Ty::Data(data) if data.data_def == self.primitives().list() => {
                // Type is already checked
                assert!(data.args.len() == 1);
                let inner_term = self.stores().args().get_element((data.args, 0)).value;
                term_as_variant!(self, self.get_term(inner_term), Ty)
            }
            Ty::Hole(_) => self.new_ty_hole(),
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: {
                        self.new_ty(DataTy {
                            data_def: self.primitives().list(),
                            args: self.new_args(&[self.new_term(self.new_ty_hole())]),
                        })
                    },
                    inferred_from: Some(original_pat_id.into()),
                })
            }
        };

        let (inferred_list, inferred_list_inner_ty) =
            self.infer_unified_pat_list(list_pat.pats, list_annotation_inner_ty)?;
        let list_ty = DataTy {
            data_def: self.primitives().list(),
            args: self.new_args(&[self.new_term(inferred_list_inner_ty)]),
        };
        Ok((ArrayPat { pats: inferred_list, spread: list_pat.spread }, list_ty))
    }

    /// Infer a constructor pattern
    pub fn infer_ctor_pat(
        &self,
        pat: &CtorPat,
        annotation_ty: TyId,
        original_pat_id: PatId,
    ) -> TcResult<(CtorPat, DataTy)> {
        let ctor = self.stores().ctor_defs().map_fast(pat.ctor.0, |defs| defs[pat.ctor.1]);
        let data_def = self.get_data_def(ctor.data_def_id);

        let norm = self.normalisation_ops();
        let reduced_ty = norm.to_ty(norm.normalise(annotation_ty.into())?);

        let annotation_data_ty = match self.get_ty(reduced_ty) {
            Ty::Data(data) if data.data_def == ctor.data_def_id => Some(data),
            Ty::Hole(_) => None,
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: self.new_ty(DataTy { args: pat.data_args, data_def: ctor.data_def_id }),
                    inferred_from: Some(original_pat_id.into()),
                });
            }
        };

        self.context().enter_scope(ScopeKind::Ctor(pat.ctor), || {
            let (inferred_data_args, inferred_data_def_params) =
                self.infer_args(pat.data_args, data_def.params)?;
            self.context_utils().add_arg_bindings(inferred_data_def_params, inferred_data_args);

            let (inferred_ctor_args, _) =
                self.infer_pat_args(pat.ctor_pat_args, pat.ctor_pat_args_spread, ctor.params)?;

            // Try to unify given annotation with inferred eventual type.
            let result_data_def_args = match annotation_data_ty {
                Some(data_ty) => {
                    self.unification_ops().unify_args(data_ty.args, ctor.result_args)?.result
                }
                None => ctor.result_args,
            };

            // Evaluate the result args.
            Ok((
                CtorPat {
                    ctor: ctor.id,
                    data_args: result_data_def_args,
                    ctor_pat_args: inferred_ctor_args,
                    ctor_pat_args_spread: pat.ctor_pat_args_spread,
                },
                DataTy { args: result_data_def_args, data_def: data_def.id },
            ))
        })
    }

    /// Infer an or-pattern
    pub fn infer_or_pat(&self, pat: &OrPat, annotation_ty: TyId) -> TcResult<(OrPat, TyId)> {
        let (result_list, result_list_ty) =
            self.infer_unified_pat_list(pat.alternatives, annotation_ty)?;
        Ok((OrPat { alternatives: result_list }, result_list_ty))
    }

    /// Infer an if-pattern
    pub fn infer_if_pat(&self, pat: &IfPat, annotation_ty: TyId) -> TcResult<(IfPat, TyId)> {
        let (inner_pat, ty) = self.infer_pat(pat.pat, annotation_ty)?;
        let (cond, _) =
            self.infer_term(pat.condition, self.new_data_ty(self.primitives().bool()))?;
        Ok((IfPat { pat: inner_pat, condition: cond }, ty))
    }

    /// Infer the type of a pattern, and return it.
    pub fn infer_pat(&self, pat_id: PatId, annotation_ty: TyId) -> TcResult<(PatId, TyId)> {
        self.register_new_atom(pat_id, annotation_ty);

        let result =
            match self.get_pat(pat_id) {
                Pat::Binding(_) => (pat_id, annotation_ty),
                Pat::Range(range_pat) => (pat_id, self.infer_range_pat(range_pat, annotation_ty)?),
                Pat::Lit(lit) => (pat_id, self.infer_lit(&lit.into(), annotation_ty)?.1),
                Pat::Tuple(tuple_pat) => self.generalise_pat_and_ty_inference(
                    self.infer_tuple_pat(&tuple_pat, annotation_ty, pat_id)?,
                ),
                Pat::Array(list_term) => self.generalise_pat_and_ty_inference(
                    self.infer_list_pat(&list_term, annotation_ty, pat_id)?,
                ),
                Pat::Ctor(ctor_pat) => self.generalise_pat_and_ty_inference(self.infer_ctor_pat(
                    &ctor_pat,
                    annotation_ty,
                    pat_id,
                )?),
                Pat::Or(or_pat) => {
                    self.generalise_pat_inference(self.infer_or_pat(&or_pat, annotation_ty)?)
                }
                Pat::If(if_pat) => {
                    self.generalise_pat_inference(self.infer_if_pat(&if_pat, annotation_ty)?)
                }
            };

        self.register_atom_inference(pat_id, result.0, result.1);
        Ok(result)
    }

    /// Infer the given constructor definition.
    pub fn infer_ctor_def(&self, ctor: CtorDefId) -> TcResult<()> {
        self.context().enter_scope(ctor.into(), || {
            let (ctor_data_def_id, ctor_params, ctor_result_args) =
                self.stores().ctor_defs().map_fast(ctor.0, |ctors| {
                    (ctors[ctor.1].data_def_id, ctors[ctor.1].params, ctors[ctor.1].result_args)
                });

            // Infer the parameters and return type of the data type
            let params = self.infer_params(ctor_params, ctor.into())?;
            let return_ty =
                self.new_ty(DataTy { data_def: ctor_data_def_id, args: ctor_result_args });
            let (return_ty, _) = self.infer_ty(return_ty, self.new_ty_hole())?;
            let return_ty_args = ty_as_variant!(self, self.get_ty(return_ty), Data).args;

            self.stores().ctor_defs().modify_fast(ctor.0, |ctors| {
                ctors[ctor.1].params = params;
                ctors[ctor.1].result_args = return_ty_args;
            });

            Ok(())
        })
    }

    /// Infer the given data definition.
    pub fn infer_data_def(&self, data_def_id: DataDefId) -> TcResult<()> {
        self.context().enter_scope(data_def_id.into(), || {
            let (data_def_params, data_def_ctors) = self
                .stores()
                .data_def()
                .map_fast(data_def_id, |data_def| (data_def.params, data_def.ctors));

            let inferred_params = self.infer_params(data_def_params, data_def_id.into())?;

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
                    PrimitiveCtorInfo::Array(array_ctor_info) => {
                        // Infer the inner type
                        let element_ty =
                            self.infer_ty(array_ctor_info.element_ty, self.new_ty_hole())?.0;
                        self.stores().data_def().modify_fast(data_def_id, |def| {
                            def.ctors =
                                DataDefCtors::Primitive(PrimitiveCtorInfo::Array(ListCtorInfo {
                                    element_ty,
                                }));
                        });
                        Ok(())
                    }
                },
            }
        })
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
                self.infer_fn_def(fn_def_id, self.new_ty_hole(), self.new_term_hole())?;
                Ok(())
            }
        }
    }

    /// Infer the given module definition.
    pub fn infer_mod_def(&self, mod_def_id: ModDefId) -> TcResult<()> {
        self.context().enter_scope(mod_def_id.into(), || {
            let members = self.stores().mod_def().map_fast(mod_def_id, |def| def.members);
            let mut error_state = self.new_error_state();

            // Infer each member
            for member_idx in members.to_index_range() {
                let _ = error_state.try_or_add_error(self.infer_mod_member((members, member_idx)));
            }

            self.return_or_register_errors(|| Ok(()), error_state)
        })
    }
}
