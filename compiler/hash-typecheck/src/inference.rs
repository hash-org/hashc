//! Operations to infer types of terms and patterns.

use derive_more::{Constructor, Deref};
use hash_ast::ast::{FloatLitKind, IntLitKind};
use hash_intrinsics::utils::PrimitiveUtils;
use hash_reporting::diagnostic::Diagnostics;
use hash_source::{
    constant::{FloatTy, IntTy, SIntTy, UIntTy, CONSTANT_MAP},
    entry_point::EntryPointKind,
    identifier::IDENTS,
    ModuleKind,
};
use hash_tir::{
    access::AccessTerm,
    args::{ArgData, ArgId, ArgsId, PatArgData, PatArgsId, PatOrCapture},
    arrays::{ArrayPat, ArrayTerm, IndexTerm},
    atom_info::ItemInAtomInfo,
    casting::CastTerm,
    control::{IfPat, LoopControlTerm, LoopTerm, MatchCase, MatchTerm, OrPat, ReturnTerm},
    data::{
        ArrayCtorInfo, CtorDefId, CtorPat, CtorTerm, DataDefCtors, DataDefId, DataTy,
        PrimitiveCtorInfo,
    },
    directives::DirectiveTarget,
    environment::{
        context::{ParamOrigin, ScopeKind},
        env::AccessToEnv,
    },
    fns::{FnBody, FnCallTerm, FnDefId, FnTy},
    lits::Lit,
    mods::{ModDefId, ModMemberId, ModMemberValue},
    params::{Param, ParamData, ParamsId},
    pats::{Pat, PatId, PatListId, RangePat, Spread},
    refs::{DerefTerm, RefTerm, RefTy},
    scopes::{AssignTerm, BlockTerm, DeclTerm},
    sub::Sub,
    symbols::Symbol,
    term_as_variant,
    terms::{Term, TermId, TermListId, UnsafeTerm},
    tuples::{TuplePat, TupleTerm, TupleTy},
    ty_as_variant,
    tys::{Ty, TyId, TypeOfTerm},
    utils::{common::CommonUtils, AccessToUtils},
};
use hash_utils::{
    itertools::Itertools,
    store::{CloneStore, PartialCloneStore, SequenceStore, SequenceStoreKey, Store},
};

use super::unification::Uni;
use crate::{
    errors::{TcError, TcResult, WrongTermKind},
    AccessToTypechecking,
};

/// The mode in which to infer the type of a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnInferMode {
    /// Infer the type of a function but do not look at its body.
    Header,
    /// Infer the type of a function and its body.
    Body,
}

/// The result of inferring the annotation of an item.
///
/// I.e. type of a term, type of a pattern, params of args, etc.
#[derive(Debug, Clone)]
pub struct Inference<X, T>(
    // /// A substitution occurring from the inference.
    // pub sub: Sub,
    /// The result of the inference, with the substitution applied.
    pub X,
    /// The annotation of the result, with the substitution applied.
    pub T,
);

impl<X, T> From<Inference<X, T>> for (X, T) {
    fn from(Inference(x, t): Inference<X, T>) -> (X, T) {
        (x, t)
    }
}

#[derive(Constructor, Deref)]
pub struct InferenceOps<'a, T: AccessToTypechecking>(&'a T);

impl<T: AccessToTypechecking> InferenceOps<'_, T> {
    /// Infer the given generic arguments (specialised
    /// for args and pat args below).
    pub fn infer_some_args<Arg: Clone>(
        &self,
        args: impl Iterator<Item = Arg>,
        annotation_params: ParamsId,
        mut infer_arg: impl FnMut(&Arg, &Param) -> TcResult<Inference<Arg, ParamData>>,
        get_arg_id: impl Fn(usize) -> Option<ArgId>,
        get_arg_value: impl Fn(&Arg) -> Option<TermId>,
    ) -> TcResult<Inference<Vec<Arg>, ParamsId>> {
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
                Some(Inference(inferred_arg, inferred_param)) => {
                    // Extend the running substitution with the new unification result
                    if let Some(arg_value) = get_arg_value(&inferred_arg) {
                        running_sub.insert(param.name, arg_value);
                    }

                    collected_args.push(inferred_arg);

                    // If the original parameter has holes, then we use the
                    // inferred parameter. Otherwise use the original parameter. @@Correctness: do
                    // we need to unify here?
                    if self.substitution_ops().atom_has_holes(param.ty).is_some() {
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
            || {
                Ok(Inference(
                    collected_args,
                    self.param_utils().create_params(collected_params.into_iter()),
                ))
            },
            error_state,
        )
    }

    /// Infer the type of a sequence of terms which should all match.
    pub fn infer_unified_list<U: Copy>(
        &self,
        items: &[U],
        item_annotation_ty: TyId,
        infer_item: impl Fn(U, TyId) -> TcResult<Inference<U, TyId>>,
        sub_item: impl Fn(U, &Sub) -> U,
    ) -> TcResult<Inference<Vec<U>, TyId>> {
        let mut current_ty = item_annotation_ty;
        let mut error_state = self.new_error_state();
        let mut results = vec![];

        for &item in items {
            match infer_item(item, item_annotation_ty) {
                Ok(Inference(inferred_item, ty)) => {
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

        self.return_or_register_errors(|| Ok(Inference(results, current_ty)), error_state)
    }

    /// Infer the given term list as one type.
    ///
    /// Returns the inferred list, and its inferred type.
    pub fn infer_unified_term_list(
        &self,
        term_list_id: TermListId,
        element_annotation_ty: TyId,
    ) -> TcResult<Inference<TermListId, TyId>> {
        let terms = self.stores().term_list().get_vec(term_list_id);
        let Inference(inferred_term_vec, inferred_ty_id) = self.infer_unified_list(
            &terms,
            element_annotation_ty,
            |term, ty| self.infer_term(term, ty),
            |term, sub| self.substitution_ops().apply_sub_to_term(term, sub),
        )?;
        Ok(Inference(self.new_term_list(inferred_term_vec), inferred_ty_id))
    }

    /// Infer the given pattern list as one type.
    ///
    /// Returns the inferred list, and its inferred type.
    pub fn infer_unified_pat_list(
        &self,
        pat_list_id: PatListId,
        element_annotation_ty: TyId,
    ) -> TcResult<Inference<PatListId, TyId>> {
        let pats = self.stores().pat_list().get_vec(pat_list_id);
        let Inference(inferred_pat_vec, inferred_ty_id) = self.infer_unified_list(
            &pats,
            element_annotation_ty,
            |pat, ty| match pat {
                PatOrCapture::Pat(pat) => {
                    let Inference(pat, ty) = self.infer_pat(pat, ty)?;
                    Ok(Inference(PatOrCapture::Pat(pat), ty))
                }
                PatOrCapture::Capture => Ok(Inference(PatOrCapture::Capture, ty)),
            },
            |pat, sub| match pat {
                PatOrCapture::Pat(pat) => {
                    let pat = self.substitution_ops().apply_sub_to_pat(pat, sub);
                    PatOrCapture::Pat(pat)
                }
                PatOrCapture::Capture => PatOrCapture::Capture,
            },
        )?;
        Ok(Inference(self.new_pat_list(inferred_pat_vec), inferred_ty_id))
    }

    /// Infer the given arguments, producing inferred parameters.
    pub fn infer_args(
        &self,
        args: ArgsId,
        annotation_params: ParamsId,
    ) -> TcResult<Inference<ArgsId, ParamsId>> {
        self.register_new_atom(args, annotation_params);

        let reordered_args_id =
            self.param_ops().validate_and_reorder_args_against_params(args, annotation_params)?;
        let reordered_args = self.stores().args().map_fast(reordered_args_id, |args| {
            args.iter().map(|arg| ArgData { target: arg.target, value: arg.value }).collect_vec()
        });

        let Inference(inferred_args, inferred_params_id) = self.infer_some_args(
            reordered_args.iter().copied(),
            annotation_params,
            |arg, param| {
                let Inference(term, ty) = self.infer_term(arg.value, param.ty)?;
                Ok(Inference(
                    ArgData { target: arg.target, value: term },
                    ParamData { name: param.name, ty, default: param.default },
                ))
            },
            |i| Some((reordered_args_id, i)),
            |arg| Some(arg.value),
        )?;

        let inferred_args_id = self.param_utils().create_args(inferred_args.into_iter());

        self.register_atom_inference_indexed(args, inferred_args_id, inferred_params_id);
        Ok(Inference(inferred_args_id, inferred_params_id))
    }

    /// Infer the given pattern arguments, producing inferred parameters.
    pub fn infer_pat_args(
        &self,
        pat_args: PatArgsId,
        spread: Option<Spread>,
        annotation_params: ParamsId,
    ) -> TcResult<Inference<PatArgsId, ParamsId>> {
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

        let Inference(inferred_pat_args, inferred_params_id) = self.infer_some_args(
            pat_args_data.iter().copied(),
            annotation_params,
            |pat_arg, param| match pat_arg.pat {
                PatOrCapture::Pat(pat) => {
                    let Inference(pat, ty) = self.infer_pat(pat, param.ty)?;
                    Ok(Inference(
                        PatArgData {
                            target: self.get_param_index(param.id),

                            pat: PatOrCapture::Pat(pat),
                        },
                        ParamData { name: param.name, ty, default: param.default },
                    ))
                }
                PatOrCapture::Capture => Ok(Inference(
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

        // @@Fix: add back spread to inferred pat args
        self.register_atom_inference_indexed(pat_args, inferred_pat_args_id, inferred_params_id);
        Ok(Inference(inferred_pat_args_id, inferred_params_id))
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
            if let Some(Inference(ty, _)) =
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
                let Inference(checked_ty, _) = self.infer_ty(ty, self.new_ty_hole())?;
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
    ) -> TcResult<Inference<TupleTerm, TupleTy>> {
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

        let Inference(inferred_args, inferred_params) = self.context().enter_scope(
            ScopeKind::TupleTy(TupleTy { data: params }),
            || -> TcResult<_> {
                let args = self.infer_args(term.data, params)?;
                Ok(args)
            },
        )?;

        Ok(Inference(TupleTerm { data: inferred_args }, TupleTy { data: inferred_params }))
    }

    /// Potentially adjust the underlying constant of a literal after its type
    /// has been inferred.
    ///
    /// This might be needed if a literal is unsuffixed in the original source,
    /// and thus represented as something other than its true type in the
    /// `CONSTANT_MAP`. After `infer_lit`, its true type will be known, and
    /// we can then adjust the underlying constant to match the true type.
    fn adjust_lit_repr(&self, lit: &Lit, inferred_ty: TyId) -> TcResult<()> {
        // @@Future: we could defer parsing these literals until we have inferred their
        // type, and here we can then check that the literal is compatible with
        // the inferred type, and then we create the constant, avoiding much of
        // the complexity here.
        match lit {
            Lit::Float(float_lit) => {
                if let Some(float_ty) = self.try_use_ty_as_float_ty(inferred_ty) {
                    CONSTANT_MAP.adjust_float(float_lit.underlying.value, float_ty);
                }
                // @@Incomplete: it is possible that exotic literal
                // types are defined, what happens then?
            }
            Lit::Int(int_lit) => {
                if let Some(int_ty) = self.try_use_ty_as_int_ty(inferred_ty) {
                    CONSTANT_MAP.adjust_int(
                        int_lit.underlying.value,
                        int_ty,
                        self.env().target().pointer_bit_width / 8,
                    );
                }
                // @@Incomplete: as above
            }
            _ => {}
        }
        Ok(())
    }

    /// Infer the type of a literal.
    pub fn infer_lit(&self, lit: &Lit, annotation_ty: TyId) -> TcResult<Inference<Lit, TyId>> {
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

        let inferred_ty = self.check_by_unify(inferred_ty, annotation_ty)?;
        self.adjust_lit_repr(lit, inferred_ty)?;
        Ok(Inference(*lit, inferred_ty))
    }

    /// Infer the type of a primitive term.
    pub fn infer_array_term(
        &self,
        array_term: &ArrayTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<Inference<ArrayTerm, TyId>> {
        let normalised_ty = self.normalise_and_check_ty(annotation_ty)?;

        let mismatch = || {
            Err(TcError::MismatchingTypes {
                expected: annotation_ty,
                actual: {
                    self.new_ty(DataTy {
                        data_def: self.primitives().list(),
                        args: self.new_args(&[self.new_term(self.new_ty_hole())]),
                    })
                },
                inferred_from: Some(original_term_id.into()),
            })
        };

        let (list_annotation_inner_ty, list_len) = match self.get_ty(normalised_ty) {
            Ty::Data(data) => {
                let data_def = self.get_data_def(data.data_def);

                match data_def.ctors {
                    DataDefCtors::Primitive(primitive) => {
                        if let PrimitiveCtorInfo::Array(array_prim) = primitive {
                            // First infer the data arguments
                            let Inference(inferred_data_args, inferred_data_params) =
                                self.infer_args(data.args, data_def.params)?;

                            let param_uni = self
                                .unification_ops()
                                .unify_params(
                                    inferred_data_params,
                                    data_def.params,
                                    ParamOrigin::Data(data_def.id),
                                )
                                .unwrap();

                            // Create a substitution from the inferred data arguments
                            let data_sub = self
                                .substitution_ops()
                                .create_sub_from_args_of_params(inferred_data_args, data_def.params)
                                .join(&param_uni.sub);

                            self.context().enter_scope(data_def.id.into(), || {
                                let subbed_element_ty = self
                                    .substitution_ops()
                                    .apply_sub_to_ty(array_prim.element_ty, &data_sub);

                                let subbed_index = array_prim.length.map(|l| {
                                    self.substitution_ops().apply_sub_to_term(l, &data_sub)
                                });

                                Ok((subbed_element_ty, subbed_index))
                            })
                        } else {
                            mismatch()
                        }
                    }
                    _ => mismatch(),
                }
            }
            Ty::Hole(_) => Ok((self.new_ty_hole(), None)),
            _ => mismatch(),
        }?;

        let Inference(inferred_list, inferred_list_inner_ty) =
            self.infer_unified_term_list(array_term.elements, list_annotation_inner_ty)?;

        // Ensure the array lengths match if given
        if let Some(len) = list_len {
            let inferred_len_term = self.create_term_from_integer_lit(inferred_list.len());
            if !self.unification_ops().terms_are_equal(len, inferred_len_term) {
                return Err(TcError::MismatchingArrayLengths {
                    expected_len: len,
                    got_len: inferred_len_term,
                });
            }
        }

        // Unify the inner annotation type with the inferred type
        let inner_ty_uni =
            self.unification_ops().unify_tys(inferred_list_inner_ty, list_annotation_inner_ty)?;

        // Either create a default list type or apply the substitution to the annotation
        // type
        let list_ty = match self.get_ty(normalised_ty) {
            Ty::Hole(_) => {
                let list_ty = self.new_ty(DataTy {
                    data_def: self.primitives().list(),
                    args: self.new_args(&[self.new_term(inner_ty_uni.result)]),
                });

                self.unification_ops().unify_tys(normalised_ty, list_ty)?.result
            }
            _ => self.substitution_ops().apply_sub_to_ty(normalised_ty, &inner_ty_uni.sub),
        };

        Ok(Inference(ArrayTerm { elements: inferred_list }, list_ty))
    }

    /// Infer a constructor term.
    pub fn infer_ctor_term(
        &self,
        term: &CtorTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<Inference<CtorTerm, DataTy>> {
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
            let Inference(inferred_data_args, inferred_data_params) =
                self.infer_args(data_args_uni.result, data_def.params)?;

            let param_uni = self
                .unification_ops()
                .unify_params(inferred_data_params, data_def.params, ParamOrigin::Data(data_def.id))
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
                let Inference(inferred_ctor_args, inferred_ctor_params) =
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
                Ok(Inference(
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
    ) -> TcResult<Inference<FnCallTerm, TyId>> {
        let Inference(subject_term, subject_ty) =
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
                        let Inference(inferred_fn_call_args, inferred_params) =
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

                        let subject = self.substitution_ops().apply_sub_to_term(
                            self.substitution_ops().apply_sub_to_term(subject_term, &param_uni.sub),
                            &uni.sub,
                        );
                        let subject_ty = self.substitution_ops().apply_sub_to_ty(
                            self.substitution_ops().apply_sub_to_ty(subject_ty, &param_uni.sub),
                            &uni.sub,
                        );
                        self.register_atom_inference(fn_call_term.subject, subject, subject_ty);

                        Ok(Inference(
                            FnCallTerm {
                                subject,
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

    /// Flag the given function as an entry point if it is one.
    ///
    /// This is done by checking if the function is named "main" or if it has
    /// the #entry_point directive.
    pub fn potentially_flag_fn_as_entry_point(&self, fn_def_id: FnDefId) -> TcResult<()> {
        if self.entry_point().has() {
            return Ok(());
        }

        let fn_def_symbol = self.stores().fn_def().map_fast(fn_def_id, |f| f.name);
        let fn_def_name = self.get_symbol(fn_def_symbol).name.unwrap();

        // Find the entry point either by name "main" or by the #entry_point directive.
        let entry_point = if self
            .stores()
            .directives()
            .get(fn_def_id.into())
            .map(|x| x.contains(IDENTS.entry_point))
            == Some(true)
        {
            Some(EntryPointKind::Named(fn_def_name))
        } else if fn_def_name == IDENTS.main
            && self.source_map().module_kind_by_id(self.current_source_info().source_id())
                == Some(ModuleKind::EntryPoint)
        {
            Some(EntryPointKind::Main)
        } else {
            None
        };

        if let Some(entry_point) = entry_point {
            // Ensure it is well-typed
            let call_term = self.new_term(FnCallTerm {
                subject: self.new_term(fn_def_id),
                implicit: false,
                args: self.new_empty_args(),
            });

            let _ = self.infer_term(call_term, self.new_ty_hole())?;

            // If successful, flag it as an entry point.
            self.entry_point().set(fn_def_id, entry_point);
        }

        Ok(())
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
        fn_mode: FnInferMode,
    ) -> TcResult<Inference<FnDefId, FnTy>> {
        // Already inferred
        if let Some(inferred_fn_def_id) = self.try_get_inferred_value(fn_def_id) {
            return Ok(Inference(inferred_fn_def_id, self.get_inferred_ty(inferred_fn_def_id)));
        }

        let fn_def = self.stores().fn_def().get(fn_def_id);

        // Atom is already registered but not inferred, it means we are in a
        // recursive call.
        if self.atom_is_registered(fn_def_id) && fn_mode == FnInferMode::Body {
            return Ok(Inference(fn_def_id, fn_def.ty));
        }

        if fn_mode == FnInferMode::Body {
            self.register_new_atom(fn_def_id, fn_def.ty);
        }

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

                    // Helper to infer the given body with the given annotation,
                    // with special handling for the first pass.
                    //
                    // In the first pass, we just infer the function type (and potential curried
                    // functions). In the second pass, we infer the body too.
                    let infer_body_if_not_first_pass = |body: TermId, ty: TyId| match fn_mode {
                        FnInferMode::Header => match self.get_term(body) {
                            Term::FnRef(immediate_body_fn) => self
                                .infer_fn_def(
                                    immediate_body_fn,
                                    annotation_ty,
                                    body,
                                    FnInferMode::Header,
                                )
                                .map(|i| self.generalise_term_and_ty_inference(i)),
                            _ => Ok(Inference(body, ty)),
                        },
                        _ => {
                            let inferred_body = self.infer_term(body, ty)?;

                            // Inferring the body might re-set the function type, so we need to
                            // re-get it.
                            let return_ty_set_from_return_statement =
                                self.get_fn_def(fn_def_id).ty.return_ty;

                            Ok(Inference(
                                inferred_body.0,
                                self.check_by_unify(
                                    inferred_body.1,
                                    return_ty_set_from_return_statement,
                                )?,
                            ))
                        }
                    };

                    // Ensure that the return types match
                    let Inference(inferred_ret, inferred_ret_ty) =
                        if let Some(annotation_fn_ty) = annotation_fn_ty {
                            let subbed_annotation_ty = self.substitution_ops().apply_sub_to_ty(
                                annotation_fn_ty.return_ty,
                                &inferred_params_result.sub,
                            );

                            let unified_return_ty = self
                                .unification_ops()
                                .unify_tys(fn_def.ty.return_ty, subbed_annotation_ty)?;

                            infer_body_if_not_first_pass(fn_body, unified_return_ty.result)?
                        } else {
                            infer_body_if_not_first_pass(fn_body, fn_def.ty.return_ty)?
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

                    if fn_mode == FnInferMode::Body {
                        self.register_atom_inference(fn_def_id, fn_def_id, inferred_fn_ty);
                    }

                    Ok(Inference(fn_def_id, inferred_fn_ty))
                })
            }
            FnBody::Intrinsic(_) | FnBody::Axiom => {
                if fn_mode == FnInferMode::Body {
                    self.register_atom_inference(fn_def_id, fn_def_id, fn_def.ty);
                }
                Ok(Inference(fn_def_id, fn_def.ty))
            }
        }
    }

    /// Infer the type of a variable, and return it.
    pub fn infer_var(&self, term: Symbol, annotation_ty: TyId) -> TcResult<TyId> {
        let normalised_annotation_ty = self.normalise_and_check_ty(annotation_ty)?;
        match self.context().try_get_binding(term) {
            Some(_) => {
                let binding_ty = self.context_utils().get_binding_ty(term);
                self.check_by_unify(binding_ty, normalised_annotation_ty)
            }
            None => {
                if self.diagnostics().has_errors() {
                    Ok(self.new_ty_hole())
                } else {
                    panic!("no binding found for symbol '{}'", self.env().with(term))
                }
            }
        }
    }

    /// Infer the type of a `return` term, and return it.
    pub fn infer_return_term(
        &self,
        return_term: &ReturnTerm,
        annotation_ty: TyId,
    ) -> TcResult<Inference<ReturnTerm, TyId>> {
        let closest_fn_def = self.context_utils().get_first_fn_def_in_scope();
        match closest_fn_def {
            Some(closest_fn_def) => {
                // Get the closest fn def in scope, and unify the
                // inferred expression type with its return type.
                // If successful, modify the fn def to set the return type to the inferred type.
                let closest_fn_def_return_ty =
                    self.stores().fn_def().map_fast(closest_fn_def, |def| def.ty.return_ty);

                let Inference(inferred_return_term, inferred_return_ty) =
                    self.infer_term(return_term.expression, closest_fn_def_return_ty)?;

                self.stores()
                    .fn_def()
                    .modify_fast(closest_fn_def, |def| def.ty.return_ty = inferred_return_ty);

                let inferred_ty = self.new_never_ty();
                Ok(Inference(
                    ReturnTerm { expression: inferred_return_term },
                    self.check_by_unify(inferred_ty, annotation_ty)?,
                ))
            }
            None => panic!("no fn def found in scope for return term"),
        }
    }

    /// Infer the type of a deref term, and return it.
    pub fn infer_deref_term(
        &self,
        deref_term: &DerefTerm,
        annotation_ty: TyId,
    ) -> TcResult<Inference<DerefTerm, TyId>> {
        let Inference(subject_term, subject_ty) =
            self.infer_term(deref_term.subject, self.new_ty_hole())?;

        let inferred_ty = match self.get_ty(subject_ty) {
            Ty::Ref(ref_ty) => ref_ty.ty,
            _ => {
                return Err(TcError::CannotDeref {
                    subject: subject_term,
                    actual_subject_ty: subject_ty,
                })
            }
        };

        Ok(Inference(
            DerefTerm { subject: subject_term },
            self.check_by_unify(inferred_ty, annotation_ty)?,
        ))
    }

    /// Infer the type of a type, and return it.
    pub fn infer_ty(&self, ty_id: TyId, annotation_ty: TyId) -> TcResult<Inference<TyId, TyId>> {
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
                let Inference(inner_ty, _) = self.infer_ty(ref_ty.ty, self.new_ty_hole())?;
                Ok((
                    self.new_ty(RefTy { ty: inner_ty, kind: ref_ty.kind, mutable: ref_ty.mutable }),
                    self.new_small_universe_ty(),
                ))
            }
            Ty::Data(data_ty) => {
                self.context().enter_scope(ScopeKind::Data(data_ty.data_def), || {
                    let data_def = self.get_data_def(data_ty.data_def);
                    let Inference(inferred_data_args, _) =
                        self.infer_args(data_ty.args, data_def.params)?;

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
        self.potentially_dump_tir(result_ty.0);
        Ok(Inference(result_ty.0, self.check_by_unify(result_ty.1, annotation_ty)?))
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
    ) -> TcResult<Inference<UnsafeTerm, TyId>> {
        // @@Todo: unsafe context
        // For now just forward to the inner term.
        Ok(Inference(*unsafe_term, self.infer_term(unsafe_term.inner, annotation_ty)?.1))
    }

    /// Infer the type of a loop term, and return it.
    pub fn infer_loop_term(
        &self,
        loop_term: &LoopTerm,
        annotation_ty: TyId,
    ) -> TcResult<Inference<LoopTerm, TyId>> {
        // Forward to the inner term.
        let Inference(inferred_block_term, _) =
            self.infer_block_term(&loop_term.block, self.new_ty_hole())?;
        Ok(Inference(
            LoopTerm { block: inferred_block_term },
            self.check_by_unify(self.new_void_ty(), annotation_ty)?,
        ))
    }

    /// Infer the type of a block term, and return it.
    pub fn infer_block_term(
        &self,
        block_term: &BlockTerm,
        annotation_ty: TyId,
    ) -> TcResult<Inference<BlockTerm, TyId>> {
        self.stores().term_list().map(block_term.statements, |statements| {
            self.context().enter_scope(block_term.stack_id.into(), || {
                // Handle local mod def
                let stack = self.stores().stack().get(block_term.stack_id);
                if let Some(local_mod_def) = stack.local_mod_def {
                    // @@Improvement: it would be nice to pass through local
                    // mod defs in two stages as well.
                    self.infer_mod_def(local_mod_def, FnInferMode::Body)?;
                }

                // Keep track of statements diverging, so we can infer the appropirate return
                // type.
                let mut diverges = false;

                let mut inferred_statements = vec![];
                for &statement in statements {
                    let Inference(inferred_statement, inferred_statement_ty) =
                        self.infer_term(statement, self.new_ty_hole())?;
                    inferred_statements.push(inferred_statement);

                    // If the statement diverges, we can already exit
                    if self.unification_ops().is_uninhabitable(inferred_statement_ty)? {
                        diverges = true;
                        break;
                    }
                }

                let (return_term, return_ty) = if diverges {
                    // If it diverges, we can just infer the return type as `never`.
                    self.new_never_ty();
                    (block_term.return_value, self.new_never_ty())
                } else {
                    // Infer the return value
                    let Inference(return_term, return_ty) =
                        self.infer_term(block_term.return_value, annotation_ty)?;

                    let sub = self.substitution_ops().create_sub_from_current_stack_members();
                    let subbed_return_ty = self.substitution_ops().apply_sub_to_ty(return_ty, &sub);
                    let subbed_return_value =
                        self.substitution_ops().apply_sub_to_term(return_term, &sub);

                    (subbed_return_value, subbed_return_ty)
                };

                Ok(Inference(
                    BlockTerm {
                        statements: self.new_term_list(inferred_statements),
                        return_value: return_term,
                        stack_id: block_term.stack_id,
                    },
                    self.check_by_unify(return_ty, annotation_ty)?,
                ))
            })
        })
    }

    /// Infer a `typeof` term, and return it.
    pub fn infer_type_of_term(
        &self,
        type_of_term: TypeOfTerm,
        annotation_ty: TyId,
    ) -> TcResult<Inference<TypeOfTerm, TyId>> {
        let Inference(inferred_term, inferred_ty) =
            self.infer_term(type_of_term.term, self.new_ty_hole())?;
        let Inference(_, inferred_ty_of_ty) = self.infer_ty(inferred_ty, annotation_ty)?;
        Ok(Inference(TypeOfTerm { term: inferred_term }, inferred_ty_of_ty))
    }

    /// Infer a reference term, and return its type.
    pub fn infer_ref_term(
        &self,
        ref_term: &RefTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<Inference<RefTerm, RefTy>> {
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

        let Inference(inner_term, inner_ty) =
            self.infer_term(ref_term.subject, annotation_ref_ty.ty)?;

        Ok(Inference(
            RefTerm { subject: inner_term, ..*ref_term },
            RefTy { ty: inner_ty, ..annotation_ref_ty },
        ))
    }

    /// Infer a cast term, and return its type.
    pub fn infer_cast_term(
        &self,
        cast_term: CastTerm,
        annotation_ty: TyId,
    ) -> TcResult<Inference<CastTerm, TyId>> {
        let Inference(inferred_term, inferred_term_ty) =
            self.infer_term(cast_term.subject_term, cast_term.target_ty)?;
        let Uni { sub, .. } = self.unification_ops().unify_tys(inferred_term_ty, annotation_ty)?;
        let subbed_ty = self.substitution_ops().apply_sub_to_ty(inferred_term_ty, &sub);
        let subbed_term = self.substitution_ops().apply_sub_to_term(inferred_term, &sub);

        Ok(Inference(
            CastTerm { subject_term: subbed_term, target_ty: subbed_ty },
            inferred_term_ty,
        ))
    }

    /// Infer a stack declaration term, and return its type.
    pub fn infer_decl_term(
        &self,
        decl_term: &DeclTerm,
        annotation_ty: TyId,
    ) -> TcResult<Inference<DeclTerm, TyId>> {
        let decl_term_ty = self.normalise_and_check_ty(decl_term.ty)?;

        let (inferred_rhs_value, inferred_ty) = match decl_term.value {
            Some(value) => {
                let Inference(inferred_value, inferred_ty) =
                    self.infer_term(value, decl_term_ty)?;
                (Some(inferred_value), inferred_ty)
            }
            None => (None, decl_term_ty),
        };

        let Inference(inferred_lhs_pat, inferred_ty) =
            self.infer_pat(decl_term.bind_pat, inferred_ty)?;

        let result_decl_term = DeclTerm {
            bind_pat: inferred_lhs_pat,
            value: inferred_rhs_value,
            ty: inferred_ty,
            stack_indices: decl_term.stack_indices,
        };
        Ok(Inference(result_decl_term, self.check_by_unify(self.new_void_ty(), annotation_ty)?))
    }

    /// Infer an access term.
    pub fn infer_access_term(
        &self,
        access_term: &AccessTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<Inference<AccessTerm, TyId>> {
        let Inference(inferred_subject, inferred_subject_ty) =
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

            Ok(Inference(
                AccessTerm { subject: inferred_subject, field: access_term.field },
                unified_ty,
            ))
        } else {
            Err(TcError::PropertyNotFound {
                term: inferred_subject,
                term_ty: normalised_subject_ty,
                property: access_term.field,
            })
        }
    }

    /// Infer an index term.
    pub fn infer_index_term(
        &self,
        index_term: &IndexTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<Inference<IndexTerm, TyId>> {
        let Inference(inferred_subject, inferred_subject_ty) =
            self.infer_term(index_term.subject, self.new_ty_hole())?;
        let normalised_subject_ty = self.normalise_and_check_ty(inferred_subject_ty)?;

        // Ensure the index is a usize
        let Inference(inferred_index, _) =
            self.infer_term(index_term.index, self.new_data_ty(self.primitives().usize()))?;

        let wrong_ty = || {
            Err(TcError::WrongTy {
                term: original_term_id,
                inferred_term_ty: normalised_subject_ty,
                kind: WrongTermKind::NotAnArray,
            })
        };

        // Ensure that the subject is array-like
        let inferred_ty = match self.get_ty(normalised_subject_ty) {
            Ty::Data(data_ty) => {
                let data_def = self.get_data_def(data_ty.data_def);
                if let DataDefCtors::Primitive(PrimitiveCtorInfo::Array(array_primitive)) =
                    data_def.ctors
                {
                    let sub = self
                        .substitution_ops()
                        .create_sub_from_args_of_params(data_ty.args, data_def.params);
                    let array_ty =
                        self.substitution_ops().apply_sub_to_ty(array_primitive.element_ty, &sub);
                    Ok(array_ty)
                } else {
                    wrong_ty()
                }
            }
            _ => wrong_ty(),
        }?;

        let unified_ty = self.check_by_unify(inferred_ty, annotation_ty)?;
        Ok(Inference(IndexTerm { subject: inferred_subject, index: inferred_index }, unified_ty))
    }

    /// Infer an assign term.
    pub fn infer_assign_term(
        &self,
        assign_term: &AssignTerm,
        annotation_ty: TyId,
    ) -> TcResult<Inference<AssignTerm, TyId>> {
        let Inference(inferred_lhs, inferred_lhs_ty) =
            self.infer_term(assign_term.subject, self.new_ty_hole())?;
        let Inference(inferred_rhs, _inferred_rhs_ty) =
            self.infer_term(assign_term.value, inferred_lhs_ty)?;

        Ok(Inference(
            AssignTerm { subject: inferred_lhs, value: inferred_rhs },
            self.check_by_unify(annotation_ty, self.new_void_ty())?,
        ))
    }

    /// Infer a match term.
    pub fn infer_match_term(
        &self,
        match_term: &MatchTerm,
        annotation_ty: TyId,
    ) -> TcResult<Inference<MatchTerm, TyId>> {
        let Inference(inferred_subject, inferred_subject_ty) =
            self.infer_term(match_term.subject, self.new_ty_hole())?;
        let normalised_subject_ty = self.normalise_and_check_ty(inferred_subject_ty)?;
        let normalised_annotation_ty = self.normalise_and_check_ty(annotation_ty)?;

        let mut unified_ty = normalised_annotation_ty;
        let mut inferred_arms = Vec::new();

        for case in match_term.cases.iter() {
            // @@Todo: dependent
            let case_data = self.stores().match_cases().get_element(case);

            self.context().enter_scope(case_data.stack_id.into(), || -> TcResult<_> {
                let Inference(inferred_pat, _) =
                    self.infer_pat(case_data.bind_pat, normalised_subject_ty)?;

                let Inference(inferred_body, inferred_body_ty) =
                    self.infer_term(case_data.value, normalised_annotation_ty)?;

                let new_unified_ty = self.check_by_unify(inferred_body_ty, unified_ty)?;
                if !self.unification_ops().is_uninhabitable(new_unified_ty)? {
                    unified_ty = new_unified_ty;
                }

                inferred_arms.push(MatchCase {
                    bind_pat: inferred_pat,
                    value: inferred_body,
                    stack_id: case_data.stack_id,
                    stack_indices: case_data.stack_indices,
                });

                Ok(())
            })?
        }

        Ok(Inference(
            MatchTerm {
                cases: self.stores().match_cases().create_from_iter(inferred_arms),
                subject: inferred_subject,
            },
            unified_ty,
        ))
    }

    pub fn generalise_term_inference(
        &self,
        inference: Inference<impl Into<Term>, TyId>,
    ) -> Inference<TermId, TyId> {
        let Inference(term, ty) = inference;
        let term_id = self.new_term(term);
        Inference(term_id, ty)
    }

    pub fn generalise_term_and_ty_inference(
        &self,
        inference: Inference<impl Into<Term>, impl Into<Ty>>,
    ) -> Inference<TermId, TyId> {
        let Inference(term, ty) = inference;
        let term_id = self.new_term(term);
        let ty_id = self.new_ty(ty);
        Inference(term_id, ty_id)
    }

    pub fn generalise_pat_inference(
        &self,
        inference: Inference<impl Into<Pat>, TyId>,
    ) -> Inference<PatId, TyId> {
        let Inference(term, ty) = inference;
        let term_id = self.new_pat(term);
        Inference(term_id, ty)
    }

    pub fn generalise_pat_and_ty_inference(
        &self,
        inference: Inference<impl Into<Pat>, impl Into<Ty>>,
    ) -> Inference<PatId, TyId> {
        let Inference(term, ty) = inference;
        let term_id = self.new_pat(term);
        let ty_id = self.new_ty(ty);
        Inference(term_id, ty_id)
    }

    /// Infer a concrete type for a given term.
    ///
    /// If this is not possible, return `None`.
    /// To create a hole when this is not possible, use
    /// [`InferOps::infer_ty_of_term_or_hole`].
    pub fn infer_term(
        &self,
        term_id: TermId,
        annotation_ty: TyId,
    ) -> TcResult<Inference<TermId, TyId>> {
        self.register_new_atom(term_id, annotation_ty);

        let result = self.stores().term().map(term_id, |term| match term {
            Term::Tuple(tuple_term) => self
                .infer_tuple_term(tuple_term, annotation_ty, term_id)
                .map(|i| self.generalise_term_and_ty_inference(i)),
            Term::Lit(lit_term) => {
                self.infer_lit(lit_term, annotation_ty).map(|i| self.generalise_term_inference(i))
            }
            Term::Array(prim_term) => self
                .infer_array_term(prim_term, annotation_ty, term_id)
                .map(|i| self.generalise_term_inference(i)),
            Term::Ctor(ctor_term) => self
                .infer_ctor_term(ctor_term, annotation_ty, term_id)
                .map(|i| self.generalise_term_and_ty_inference(i)),
            Term::FnCall(fn_call_term) => self
                .infer_fn_call_term(fn_call_term, annotation_ty, term_id)
                .map(|i| self.generalise_term_inference(i)),
            Term::FnRef(fn_def_id) => self
                .infer_fn_def(*fn_def_id, annotation_ty, term_id, FnInferMode::Body)
                .map(|i| self.generalise_term_and_ty_inference(i)),
            Term::Var(var_term) => {
                Ok(Inference(term_id, self.infer_var(*var_term, annotation_ty)?))
            }
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
                Ok(Inference(term_id, self.infer_loop_control_term(loop_control_term)))
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

            Term::Index(index_term) => self
                .infer_index_term(index_term, annotation_ty, term_id)
                .map(|i| self.generalise_term_inference(i)),

            Term::Match(match_term) => self
                .infer_match_term(match_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),

            Term::Assign(assign_term) => self
                .infer_assign_term(assign_term, annotation_ty)
                .map(|i| self.generalise_term_inference(i)),

            Term::Hole(_) => Ok(Inference(term_id, annotation_ty)),
        })?;

        self.register_atom_inference(term_id, result.0, result.1);
        self.potentially_dump_tir(result.0);
        Ok(result)
    }

    /// Infer a range pattern.
    pub fn infer_range_pat(&self, range_pat: RangePat, annotation_ty: TyId) -> TcResult<TyId> {
        let Inference(_, start_ty) = self.infer_lit(&range_pat.start.into(), annotation_ty)?;
        let Inference(_, end_ty) = self.infer_lit(&range_pat.end.into(), annotation_ty)?;

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
    ) -> TcResult<Inference<TuplePat, TupleTy>> {
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

        let Inference(inferred_args, inferred_params) =
            self.context().enter_scope(ScopeKind::TupleTy(TupleTy { data: params }), || {
                self.infer_pat_args(tuple_pat.data, tuple_pat.data_spread, params)
            })?;

        Ok(Inference(
            TuplePat { data: inferred_args, data_spread: tuple_pat.data_spread },
            TupleTy { data: inferred_params },
        ))
    }

    /// Infer a list pattern
    pub fn infer_array_pat(
        &self,
        list_pat: &ArrayPat,
        annotation_ty: TyId,
        original_pat_id: PatId,
    ) -> TcResult<Inference<ArrayPat, DataTy>> {
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

        let Inference(inferred_list, inferred_list_inner_ty) =
            self.infer_unified_pat_list(list_pat.pats, list_annotation_inner_ty)?;
        let list_ty = DataTy {
            data_def: self.primitives().list(),
            args: self.new_args(&[self.new_term(inferred_list_inner_ty)]),
        };
        Ok(Inference(ArrayPat { pats: inferred_list, spread: list_pat.spread }, list_ty))
    }

    /// Infer a constructor pattern
    pub fn infer_ctor_pat(
        &self,
        pat: &CtorPat,
        annotation_ty: TyId,
        original_pat_id: PatId,
    ) -> TcResult<Inference<CtorPat, DataTy>> {
        // @@Organisation: factor out because this is almost the same for
        // infer_ctor_term
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

        let pat_data_args = if pat.data_args.len() == 0 {
            match annotation_data_ty {
                Some(t) => t.args,
                None => self.param_utils().instantiate_params_as_holes(data_def.params),
            }
        } else {
            pat.data_args
        };

        let annotation_data_ty =
            annotation_data_ty.unwrap_or(DataTy { args: pat_data_args, data_def: data_def.id });

        self.context().enter_scope(data_def.id.into(), || {
            let data_args_uni =
                self.unification_ops().unify_args(pat_data_args, annotation_data_ty.args)?;

            // First infer the data arguments
            let Inference(inferred_data_args, inferred_data_params) =
                self.infer_args(data_args_uni.result, data_def.params)?;

            let param_uni = self
                .unification_ops()
                .unify_params(inferred_data_params, data_def.params, ParamOrigin::Data(data_def.id))
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
                let Inference(inferred_ctor_pat_args, inferred_ctor_params) = self.infer_pat_args(
                    pat.ctor_pat_args,
                    pat.ctor_pat_args_spread,
                    subbed_ctor_params,
                )?;

                let ctor_ty_sub = self.unification_ops().unify_params(
                    inferred_ctor_params,
                    subbed_ctor_params,
                    ParamOrigin::Ctor(ctor.id),
                )?;

                // Apply the substitution to the constructor result args
                let subbed_result_args = self.substitution_ops().apply_sub_to_args(
                    self.substitution_ops().apply_sub_to_args(
                        self.substitution_ops().apply_sub_to_args(ctor.result_args, &param_uni.sub),
                        &data_sub,
                    ),
                    &ctor_ty_sub.sub,
                );

                // Try to unify given annotation with inferred eventual type.
                let result_data_def_args = self
                    .unification_ops()
                    .unify_args(subbed_result_args, inferred_data_args)?
                    .result;

                // Evaluate the result args.
                Ok(Inference(
                    CtorPat {
                        ctor: ctor.id,
                        data_args: result_data_def_args,
                        ctor_pat_args: inferred_ctor_pat_args,
                        ctor_pat_args_spread: pat.ctor_pat_args_spread,
                    },
                    DataTy { args: result_data_def_args, data_def: data_def.id },
                ))
            })
        })
    }

    /// Infer an or-pattern
    pub fn infer_or_pat(
        &self,
        pat: &OrPat,
        annotation_ty: TyId,
    ) -> TcResult<Inference<OrPat, TyId>> {
        let Inference(result_list, result_list_ty) =
            self.infer_unified_pat_list(pat.alternatives, annotation_ty)?;
        Ok(Inference(OrPat { alternatives: result_list }, result_list_ty))
    }

    /// Infer an if-pattern
    pub fn infer_if_pat(
        &self,
        pat: &IfPat,
        annotation_ty: TyId,
    ) -> TcResult<Inference<IfPat, TyId>> {
        let Inference(inner_pat, ty) = self.infer_pat(pat.pat, annotation_ty)?;
        let Inference(cond, _) =
            self.infer_term(pat.condition, self.new_data_ty(self.primitives().bool()))?;
        Ok(Inference(IfPat { pat: inner_pat, condition: cond }, ty))
    }

    /// Infer the type of a pattern, and return it.
    pub fn infer_pat(
        &self,
        pat_id: PatId,
        annotation_ty: TyId,
    ) -> TcResult<Inference<PatId, TyId>> {
        self.register_new_atom(pat_id, annotation_ty);

        let result =
            match self.get_pat(pat_id) {
                Pat::Binding(var) => {
                    if let Some(member) = var.stack_member {
                        self.context_utils().add_stack_binding(member, annotation_ty, None);
                    }
                    Inference(pat_id, annotation_ty)
                }
                Pat::Range(range_pat) => {
                    Inference(pat_id, self.infer_range_pat(range_pat, annotation_ty)?)
                }
                Pat::Lit(lit) => Inference(pat_id, self.infer_lit(&lit.into(), annotation_ty)?.1),
                Pat::Tuple(tuple_pat) => self.generalise_pat_and_ty_inference(
                    self.infer_tuple_pat(&tuple_pat, annotation_ty, pat_id)?,
                ),
                Pat::Array(list_term) => self.generalise_pat_and_ty_inference(
                    self.infer_array_pat(&list_term, annotation_ty, pat_id)?,
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
            let Inference(return_ty, _) = self.infer_ty(return_ty, self.new_ty_hole())?;
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
                DataDefCtors::Primitive(primitive) => {
                    match primitive {
                        PrimitiveCtorInfo::Numeric(_)
                        | PrimitiveCtorInfo::Str
                        | PrimitiveCtorInfo::Char => {
                            // Nothing to do
                            Ok(())
                        }
                        PrimitiveCtorInfo::Array(array_ctor_info) => {
                            // Infer the inner type and length
                            let element_ty =
                                self.infer_ty(array_ctor_info.element_ty, self.new_ty_hole())?.0;
                            let length = array_ctor_info
                                .length
                                .map(|l| -> TcResult<_> {
                                    Ok(self
                                        .infer_term(l, self.new_data_ty(self.primitives().usize()))?
                                        .0)
                                })
                                .transpose()?;
                            self.stores().data_def().modify_fast(data_def_id, |def| {
                                def.ctors = DataDefCtors::Primitive(PrimitiveCtorInfo::Array(
                                    ArrayCtorInfo { element_ty, length },
                                ));
                            });
                            Ok(())
                        }
                    }
                }
            }
        })
    }

    /// Dump the TIR for the given target if it has a `#dump_tir` directive
    /// applied on it.
    pub fn potentially_dump_tir(&self, target: impl Into<DirectiveTarget>) {
        let target = target.into();
        let has_dump_dir =
            self.stores().directives().get(target).map(|d| d.contains(IDENTS.dump_tir))
                == Some(true);
        if has_dump_dir {
            self.dump_tir(self.env().with(target));
        }
    }

    /// Infer the given module member.
    pub fn infer_mod_member(&self, mod_member: ModMemberId, fn_mode: FnInferMode) -> TcResult<()> {
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
                self.infer_mod_def(mod_def_id, fn_mode)?;
                Ok(())
            }
            ModMemberValue::Fn(fn_def_id) => {
                self.infer_fn_def(fn_def_id, self.new_ty_hole(), self.new_term_hole(), fn_mode)?;
                if fn_mode == FnInferMode::Body {
                    // Dump TIR if necessary
                    self.potentially_dump_tir(fn_def_id);

                    // Check for entry point
                    self.potentially_flag_fn_as_entry_point(fn_def_id)?;
                }
                Ok(())
            }
        }
    }

    /// Infer the given module definition.
    pub fn infer_mod_def(&self, mod_def_id: ModDefId, fn_mode: FnInferMode) -> TcResult<()> {
        self.context().enter_scope(mod_def_id.into(), || {
            let members = self.stores().mod_def().map_fast(mod_def_id, |def| def.members);

            let mut error_state = self.new_error_state();
            // Infer each member signature
            for member_idx in members.to_index_range() {
                let _ = error_state
                    .try_or_add_error(self.infer_mod_member((members, member_idx), fn_mode));
            }

            self.return_or_register_errors(|| Ok(()), error_state)
        })
    }
}
