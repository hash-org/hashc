//! Operations to infer types of terms and patterns.

use std::{cell::Cell, collections::HashSet, ops::ControlFlow};

use hash_attrs::{attr::attr_store, builtin::attrs};
use hash_exhaustiveness::ExhaustivenessChecker;
use hash_reporting::diagnostic::{Diagnostics, ErrorState};
use hash_source::{
    constant::{BigIntTy, FloatTy, IntTy, SIntTy, UIntTy},
    entry_point::EntryPointKind,
    identifier::IDENTS,
    ModuleKind,
};
use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_tir::{
    access::AccessTerm,
    args::{Arg, ArgId, ArgsId, PatArgsId, PatOrCapture},
    arrays::{ArrayPat, ArrayTerm, IndexTerm},
    atom_info::ItemInAtomInfo,
    casting::CastTerm,
    context::ScopeKind,
    control::{IfPat, LoopControlTerm, LoopTerm, MatchTerm, OrPat, ReturnTerm},
    data::{CtorDefId, CtorPat, CtorTerm, DataDefCtors, DataDefId, DataTy, PrimitiveCtorInfo},
    fns::{CallTerm, FnDefId, FnTy},
    intrinsics::{
        definitions::{
            bool_ty, char_def, f32_def, f64_def, i32_def, list_def, list_ty, never_ty, str_def,
            usize_ty, Intrinsic, Primitive,
        },
        make::{IsIntrinsic, IsPrimitive},
        utils::{
            bool_term, create_term_from_usize_lit, try_use_ty_as_float_ty, try_use_ty_as_int_ty,
        },
    },
    lits::{Lit, LitId},
    mods::{ModDefId, ModMemberId, ModMemberValue},
    node::{HasAstNodeId, Node, NodeId, NodeOrigin, NodesId},
    params::{
        utils::{
            validate_and_reorder_args_against_params, validate_and_reorder_pat_args_against_params,
            validate_params,
        },
        Param, ParamsId,
    },
    pats::{Pat, PatId, PatListId, RangePat, Spread},
    refs::{DerefTerm, RefTerm, RefTy},
    scopes::{AssignTerm, BlockStatement, BlockTerm},
    sub::Sub,
    symbols::SymbolId,
    term_as_variant,
    terms::{Term, TermId, TermListId, Ty, TyId, TyOfTerm, UnsafeTerm},
    tuples::{TuplePat, TupleTerm, TupleTy},
    utils::{
        common::dump_tir,
        traversing::{Atom, TraversingUtils},
    },
};
use hash_utils::derive_more::{Constructor, Deref};
use itertools::Itertools;

use crate::{
    errors::{TcError, TcResult, WrongTermKind},
    normalisation::NormalisationMode,
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

pub struct InferenceWithSub<X, T> {
    /// A substitution occurring from the inference.
    pub sub: Sub,
    /// The result of the inference, with the substitution applied.
    pub result: X,
    /// The annotation of the result, with the substitution applied.
    pub annotation: T,
}

#[derive(Constructor, Deref)]
pub struct InferenceOps<'a, T: AccessToTypechecking>(&'a T);

impl<T: AccessToTypechecking> InferenceOps<'_, T> {
    /// Create a new [ExhaustivenessChecker] so it can be used to check
    /// refutability or exhaustiveness of patterns.
    fn exhaustiveness_checker<U: HasAstNodeId>(&self, subject: U) -> ExhaustivenessChecker<'_> {
        let location = subject.span().unwrap();
        ExhaustivenessChecker::new(location, self.env())
    }

    /// Merge all of the produced diagnostics into the current diagnostics.
    ///
    /// @@Hack: remove this when we have a better way to send exhaustiveness
    /// jobs and add them to general tc diagnostics.
    fn append_exhaustiveness_diagnostics(&self, checker: ExhaustivenessChecker<'_>) {
        let (errors, warnings) = checker.into_diagnostics().into_diagnostics();

        for error in errors {
            self.diagnostics().add_error(self.convert_exhaustiveness_error(error))
        }

        for warning in warnings {
            self.diagnostics().add_warning(self.convert_exhaustiveness_warning(warning))
        }
    }

    /// Infer the given generic arguments (specialised
    /// for args and pat args below).
    ///
    /// Assumes that they are validated against one another
    pub fn infer_some_args<U, Arg: Clone>(
        &self,
        args: impl Iterator<Item = Arg>,
        annotation_params: ParamsId,
        infer_arg: impl Fn(&Arg, TyId) -> TcResult<()>,
        get_arg_value: impl Fn(&Arg) -> Option<TermId>,
        in_arg_scope: impl FnOnce() -> TcResult<U>,
    ) -> TcResult<U> {
        let (result, shadowed_sub) =
            self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
                for (arg, param_id) in args.zip(annotation_params.iter()) {
                    let param = param_id.value();
                    let param_ty = self.sub_ops().copy_term(param.ty);
                    infer_arg(&arg, param_ty)?;
                    self.sub_ops().apply_sub_to_atom_from_context(param_ty);
                    if let Some(value) = get_arg_value(&arg) {
                        self.context().add_assignment(param.name, param_ty, value);
                    }
                }
                let result = in_arg_scope()?;

                // Only keep the substitutions that do not refer to the parameters
                let scope_sub = self.sub_ops().create_sub_from_current_scope();
                let shadowed_sub =
                    self.sub_ops().hide_param_binds(annotation_params.iter(), &scope_sub);
                Ok((result, shadowed_sub))
            })?;

        // Add the shadowed substitutions to the ambient scope
        self.uni_ops().add_unification_from_sub(&shadowed_sub);
        Ok(result)
    }

    /// Infer the type of a sequence of terms which should all match.
    pub fn infer_unified_list<U: Copy>(
        &self,
        items: &[U],
        item_annotation_ty: TyId,
        infer_item: impl Fn(U, TyId) -> TcResult<()>,
    ) -> TcResult<()> {
        for &item in items {
            infer_item(item, item_annotation_ty)?;
        }
        Ok(())
    }

    /// Infer the given term list as one type.
    ///
    /// Returns the inferred list, and its inferred type.
    pub fn infer_unified_term_list(
        &self,
        term_list_id: TermListId,
        element_annotation_ty: TyId,
    ) -> TcResult<()> {
        let terms = term_list_id.value();
        self.infer_unified_list(&terms.value(), element_annotation_ty, |term, ty| {
            self.infer_term(term, ty)?;
            Ok(())
        })?;
        Ok(())
    }

    /// Infer the given pattern list as one type.
    ///
    /// Returns the inferred list, and its inferred type.
    pub fn infer_unified_pat_list(
        &self,
        pat_list_id: PatListId,
        element_annotation_ty: TyId,
    ) -> TcResult<()> {
        let pats = pat_list_id.elements().value();
        self.infer_unified_list(&pats, element_annotation_ty, |pat, ty| match pat {
            PatOrCapture::Pat(pat) => {
                self.infer_pat(pat, ty, None)?;
                Ok(())
            }
            PatOrCapture::Capture(_) => Ok(()),
        })?;
        Ok(())
    }

    /// Infer the given arguments, producing inferred parameters.
    pub fn infer_args<U>(
        &self,
        args: ArgsId,
        annotation_params: ParamsId,
        in_arg_scope: impl FnOnce(ArgsId) -> TcResult<U>,
    ) -> TcResult<U> {
        self.register_new_atom(args, annotation_params);
        let reordered_args_id = validate_and_reorder_args_against_params(args, annotation_params)?;

        let result = self.infer_some_args(
            reordered_args_id.iter(),
            annotation_params,
            |arg, param_ty| {
                let arg = arg.value();
                self.infer_term(arg.value, param_ty)?;
                Ok(())
            },
            |arg| {
                let arg = arg.value();
                Some(arg.value)
            },
            || in_arg_scope(reordered_args_id),
        )?;

        Ok(result)
    }

    pub fn try_use_pat_args_as_term_args(&self, pat_args: PatArgsId) -> Option<ArgsId> {
        let mut args = Vec::new();
        for pat_arg in pat_args.iter() {
            let pat_arg = pat_arg.value();
            match pat_arg.pat {
                PatOrCapture::Pat(pat) => {
                    let term = self.try_use_pat_as_term(pat)?;
                    args.push(Node::at(
                        Arg { target: pat_arg.target, value: term },
                        pat_arg.origin,
                    ));
                }
                PatOrCapture::Capture(_) => return None,
            }
        }
        Some(Node::create_at(Node::<Arg>::seq(args), pat_args.origin()))
    }

    pub fn try_use_pat_as_term(&self, pat_id: PatId) -> Option<TermId> {
        let origin = pat_id.origin();
        match *pat_id.value() {
            Pat::Binding(var) => Some(Term::from(var.name, origin)),
            Pat::Range(_) => Some(Term::from(SymbolId::fresh(origin), origin)),
            Pat::Lit(lit) => Some(Term::from(Term::Lit(*lit), origin)),
            Pat::Ctor(ctor_pat) => Some(Term::from(
                CtorTerm {
                    ctor: ctor_pat.ctor,
                    data_args: ctor_pat.data_args,
                    ctor_args: self.try_use_pat_args_as_term_args(ctor_pat.ctor_pat_args)?,
                },
                origin,
            )),
            Pat::Tuple(tuple_pat) => Some(Term::from(
                TupleTerm { data: self.try_use_pat_args_as_term_args(tuple_pat.data)? },
                origin,
            )),
            Pat::Array(_) => None,
            Pat::Or(_) => None,
            Pat::If(if_pat) => self.try_use_pat_as_term(if_pat.pat),
        }
    }

    /// Infer the given pattern arguments, producing inferred parameters.
    pub fn infer_pat_args<U>(
        &self,
        pat_args: PatArgsId,
        spread: Option<Spread>,
        annotation_params: ParamsId,
        in_arg_scope: impl FnOnce(PatArgsId) -> TcResult<U>,
    ) -> TcResult<U> {
        self.register_new_atom(pat_args, annotation_params);
        let reordered_pat_args_id =
            validate_and_reorder_pat_args_against_params(pat_args, spread, annotation_params)?;

        self.infer_some_args(
            reordered_pat_args_id.iter(),
            annotation_params,
            |pat_arg, param_ty| {
                let pat_arg = pat_arg.value();
                match pat_arg.pat {
                    PatOrCapture::Pat(pat) => {
                        self.infer_pat(pat, param_ty, None)?;
                        Ok(())
                    }
                    PatOrCapture::Capture(_) => Ok(()),
                }
            },
            |arg| {
                let arg = arg.value();
                match arg.pat {
                    PatOrCapture::Pat(pat) => self.try_use_pat_as_term(pat),
                    PatOrCapture::Capture(_) => None,
                }
            },
            || in_arg_scope(reordered_pat_args_id),
        )
    }

    pub fn enter_param_scope(
        &self,
        params: ParamsId,
        f: impl FnOnce() -> TcResult<()>,
    ) -> TcResult<()> {
        self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
            for param_id in params.iter() {
                let param = param_id.value();
                self.context().add_typing(param.name, param.ty);
            }
            f()
        })
    }

    /// Infer the given parameters.
    pub fn infer_params<U>(
        &self,
        params: ParamsId,
        in_param_scope: impl FnOnce() -> TcResult<U>,
    ) -> TcResult<U> {
        // Validate the parameters
        validate_params(params)?;

        let (result, shadowed_sub) =
            self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
                for param_id in params.iter() {
                    let param = param_id.value();
                    self.infer_term(param.ty, Ty::universe_of(param.ty))?;
                    self.context().add_typing(param.name, param.ty);
                }

                let result = in_param_scope()?;

                // Only keep the substitutions that do not refer to the parameters
                let scope_sub = self.sub_ops().create_sub_from_current_scope();
                let shadowed_sub = self.sub_ops().hide_param_binds(params.iter(), &scope_sub);
                Ok((result, shadowed_sub))
            })?;

        // Add the shadowed substitutions to the ambient scope
        self.uni_ops().add_unification_from_sub(&shadowed_sub);
        Ok(result)
    }

    /// Given an inferred type, and an optional annotation type, unify the two,
    /// and if the result is successful then apply the substitution to the
    /// annotation type and return it (or to the inferred type if the annotation
    /// type is not given).
    pub fn check_by_unify(&self, inferred_ty: TyId, annotation_ty: TyId) -> TcResult<()> {
        self.uni_ops().unify_terms(inferred_ty, annotation_ty)
    }

    /// Check that the given type is well-formed, and normalise it.
    pub fn check_ty(&self, ty: TyId) -> TcResult<()> {
        match *ty.value() {
            Ty::Universe | Ty::Hole(_) => Ok(()),
            _ => self.infer_term(ty, Ty::universe_of(ty)),
        }
    }

    /// Check that the given type is well-formed, and normalise it.
    pub fn normalise_and_check_ty(&self, ty: TyId) -> TcResult<()> {
        match *ty.value() {
            Ty::Hole(_) => Ok(()),
            _ => {
                self.infer_term(ty, Ty::universe_of(ty))?;
                let norm = self.norm_ops();
                norm.normalise_in_place(ty.into())?;
                Ok(())
            }
        }
    }

    /// Infer the type of a tuple term.
    pub fn infer_tuple_term(
        &self,
        tuple_term: &TupleTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        self.context().enter_scope(ScopeKind::Sub, || {
            self.normalise_and_check_ty(annotation_ty)?;
            let params = match *annotation_ty.value() {
                Ty::TupleTy(tuple_ty) => self.sub_ops().copy_params(tuple_ty.data),
                Ty::Hole(_) => Param::seq_from_args_with_hole_types(tuple_term.data),
                _ => {
                    let inferred = Param::seq_from_args_with_hole_types(tuple_term.data);
                    return Err(TcError::MismatchingTypes {
                        expected: annotation_ty,
                        actual: Ty::from(
                            TupleTy { data: inferred },
                            original_term_id.origin().inferred(),
                        ),
                    });
                }
            };

            let mut tuple_term = *tuple_term;
            self.infer_args(tuple_term.data, params, |new_args| {
                tuple_term.data = new_args;
                original_term_id.set(original_term_id.value().with_data(tuple_term.into()));
                Ok(())
            })?;

            let tuple_ty = Ty::expect_is(
                original_term_id,
                Ty::from(TupleTy { data: params }, annotation_ty.origin()),
            );
            self.check_by_unify(tuple_ty, annotation_ty)?;
            // @@Review: why is this needed? Shouldn't the substitution be applied during
            // `check_by_unify`?
            self.sub_ops().apply_sub_to_atom_from_context(annotation_ty);
            Ok(())
        })
    }

    /// Potentially adjust the underlying constant of a literal after its type
    /// has been inferred.
    ///
    /// This might be needed if a literal is unsuffixed in the original source,
    /// and thus represented as something other than its true type in the
    /// `CONSTS`. After `infer_lit`, its true type will be known, and
    /// we can then adjust the underlying constant to match the true type.
    fn bake_lit_repr(&self, lit: LitId, inferred_ty: TyId) -> TcResult<()> {
        match *lit.value() {
            Lit::Float(float_lit) => {
                // If the float is already baked, then we don't do anything.
                if float_lit.has_value() {
                    return Ok(());
                }

                if let Some(float_ty) = try_use_ty_as_float_ty(inferred_ty) {
                    lit.modify(|float| match &mut float.data {
                        Lit::Float(fl) => fl.bake(float_ty),
                        _ => unreachable!(),
                    })?;
                }
                // @@Incomplete: it is possible that exotic literal
                // types are defined, what happens then?
            }
            Lit::Int(int_lit) => {
                // If the float is already baked, then we don't do anything.
                if int_lit.has_value() {
                    return Ok(());
                }

                if let Some(int_ty) = try_use_ty_as_int_ty(inferred_ty) {
                    lit.modify(|int| match &mut int.data {
                        Lit::Int(fl) => fl.bake(self.env(), int_ty),
                        _ => unreachable!(),
                    })?;
                }
                // @@Incomplete: as above
            }
            _ => {}
        }
        Ok(())
    }

    /// Infer the type of a literal.
    pub fn infer_lit(&self, lit: LitId, annotation_ty: TyId) -> TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;
        let inferred_ty = Ty::data_ty(
            match *lit.value() {
                Lit::Int(int_lit) => {
                    match int_lit.kind() {
                        Some(ty) => match ty {
                            IntTy::Int(s_int_ty) => match s_int_ty {
                                SIntTy::I8 => Primitive::I8,
                                SIntTy::I16 => Primitive::I16,
                                SIntTy::I32 => Primitive::I32,
                                SIntTy::I64 => Primitive::I64,
                                SIntTy::I128 => Primitive::I128,
                                SIntTy::ISize => Primitive::Isize,
                            },
                            IntTy::UInt(u_int_ty) => match u_int_ty {
                                UIntTy::U8 => Primitive::U8,
                                UIntTy::U16 => Primitive::U16,
                                UIntTy::U32 => Primitive::U32,
                                UIntTy::U64 => Primitive::U64,
                                UIntTy::U128 => Primitive::U128,
                                UIntTy::USize => Primitive::Usize,
                            },
                            IntTy::Big(big_int_ty) => match big_int_ty {
                                BigIntTy::IBig => Primitive::Ibig,
                                BigIntTy::UBig => Primitive::Ubig,
                            },
                        }
                        .def(),
                        None => {
                            (match *annotation_ty.value() {
                                Ty::DataTy(data_ty) => match data_ty.data_def.value().ctors {
                                    DataDefCtors::Primitive(primitive_ctors) => {
                                        match primitive_ctors {
                                            PrimitiveCtorInfo::Numeric(numeric) => {
                                                // If the value is not compatible with the numeric
                                                // type,
                                                // then return `None` and the unification will fail.
                                                if numeric.is_float
                                                    || (!numeric.is_signed && int_lit.is_negative())
                                                {
                                                    None
                                                } else {
                                                    Some(data_ty.data_def)
                                                }
                                            }
                                            _ => None,
                                        }
                                    }
                                    DataDefCtors::Defined(_) => None,
                                },
                                _ => None,
                            })
                            .unwrap_or_else(i32_def)
                        }
                    }
                }
                Lit::Str(_) => str_def(),
                Lit::Char(_) => char_def(),
                Lit::Float(float_lit) => match float_lit.kind() {
                    Some(ty) => match ty {
                        FloatTy::F32 => f32_def(),
                        FloatTy::F64 => f64_def(),
                    },
                    None => {
                        (match *annotation_ty.value() {
                            Ty::DataTy(data_ty) => match data_ty.data_def.value().ctors {
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
                        .unwrap_or_else(f64_def)
                    }
                },
            },
            lit.origin(),
        );

        self.check_by_unify(inferred_ty, annotation_ty)?;
        self.bake_lit_repr(lit, inferred_ty)?;
        Ok(())
    }

    pub fn use_ty_as_array(&self, annotation_ty: TyId) -> TcResult<Option<(TyId, Option<TermId>)>> {
        let mismatch = || {
            Err(TcError::MismatchingTypes {
                expected: annotation_ty,
                actual: list_ty(Ty::hole(NodeOrigin::Expected), NodeOrigin::Expected),
            })
        };

        match *annotation_ty.value() {
            Ty::DataTy(data) => {
                let data_def = data.data_def.value();

                match data_def.ctors {
                    DataDefCtors::Primitive(primitive) => {
                        if let PrimitiveCtorInfo::Array(array_prim) = primitive {
                            // First infer the data arguments
                            let copied_params = self.sub_ops().copy_params(data_def.params);
                            self.infer_args(data.args, copied_params, |_| {
                                let sub = self.sub_ops().create_sub_from_current_scope();
                                let subbed_element_ty =
                                    self.sub_ops().apply_sub_to_term(array_prim.element_ty, &sub);
                                let subbed_index = array_prim
                                    .length
                                    .map(|l| self.sub_ops().apply_sub_to_term(l, &sub));
                                Ok(Some((subbed_element_ty, subbed_index)))
                            })
                        } else {
                            mismatch()
                        }
                    }
                    _ => mismatch(),
                }
            }
            Ty::Hole(_) => Ok(None),
            _ => mismatch(),
        }
    }

    /// Infer the type of a primitive term.
    pub fn infer_array_term(&self, array_term: &ArrayTerm, annotation_ty: TyId) -> TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;
        let (list_annotation_inner_ty, list_len) = self
            .use_ty_as_array(annotation_ty)?
            .unwrap_or_else(|| (Ty::hole(array_term.elements.origin().inferred()), None));

        self.infer_unified_term_list(array_term.elements, list_annotation_inner_ty)?;

        // Ensure the array lengths match if given
        if let Some(len) = list_len {
            let inferred_len_term = create_term_from_usize_lit(
                self.env(),
                array_term.elements.len(),
                array_term.elements.origin(),
            );

            if !self.uni_ops().terms_are_equal(len, inferred_len_term) {
                return Err(TcError::MismatchingArrayLengths {
                    expected_len: len,
                    got_len: inferred_len_term,
                });
            }
        }

        // Either create a default list type or apply the substitution to the annotation
        // type
        if let Ty::Hole(_) = *annotation_ty.value() {
            self.check_by_unify(
                list_ty(list_annotation_inner_ty, NodeOrigin::Expected),
                annotation_ty,
            )?
        };

        Ok(())
    }

    pub fn get_binds_in_pat_atom_once(
        &self,
        atom: Atom,
        set: &mut HashSet<SymbolId>,
    ) -> ControlFlow<()> {
        if let Atom::Pat(pat_id) = atom {
            match *pat_id.value() {
                Pat::Binding(var) => {
                    set.insert(var.name);
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            }
        } else {
            ControlFlow::Break(())
        }
    }

    pub fn get_binds_in_pat(&self, pat: PatId) -> HashSet<SymbolId> {
        let mut binds = HashSet::new();
        TraversingUtils::new()
            .visit_pat::<!, _>(pat, &mut |atom| {
                Ok(self.get_binds_in_pat_atom_once(atom, &mut binds))
            })
            .into_ok();
        binds
    }

    pub fn get_binds_in_pat_args(&self, pat_args: PatArgsId) -> HashSet<SymbolId> {
        let mut binds = HashSet::new();
        TraversingUtils::new()
            .visit_pat_args::<!, _>(pat_args, &mut |atom| {
                Ok(self.get_binds_in_pat_atom_once(atom, &mut binds))
            })
            .into_ok();
        binds
    }

    /// Infer a constructor term.
    pub fn infer_ctor_term(
        &self,
        term: &CtorTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        let mut term = *term;
        let ctor_def_id = term.ctor;
        let data_args = term.data_args;
        let original_atom: Atom = original_term_id.into();
        let ctor = ctor_def_id.value();
        let data_def = ctor.data_def_id.value();

        // Ensure the annotation is valid
        self.normalise_and_check_ty(annotation_ty)?;

        // Get the annotation as a DataTy, or create a hole one if not given
        let mut annotation_data_ty = match *annotation_ty.value() {
            Ty::DataTy(data) if data.data_def == ctor.data_def_id => DataTy {
                data_def: ctor.data_def_id,
                args: if data.args.len() == 0 {
                    Arg::seq_from_params_as_holes(data_def.params)
                } else {
                    data.args
                },
            },
            Ty::Hole(_) => DataTy {
                data_def: ctor.data_def_id,
                args: Arg::seq_from_params_as_holes(data_def.params),
            },
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: Ty::from(
                        DataTy { args: data_args, data_def: ctor.data_def_id },
                        original_term_id.origin(),
                    ),
                });
            }
        };

        // Get the data arguments given to the constructor, like Equal<...>::Refl(...)
        //                                                             ^^^ these
        let ctor_data_args = if data_args.len() == 0 {
            Arg::seq_from_params_as_holes(data_def.params)
        } else {
            data_args
        };

        // From the given constructor data args, substitute the constructor params and
        // result arguments. In the process, infer the data args more if
        // possible.
        let copied_params = self.sub_ops().copy_params(data_def.params);
        let (inferred_ctor_data_args, subbed_ctor_params, subbed_ctor_result_args) = self
            .infer_args(ctor_data_args, copied_params, |inferred_data_args| {
                let sub = self.sub_ops().create_sub_from_current_scope();
                let subbed_ctor_params = self.sub_ops().apply_sub_to_params(ctor.params, &sub);
                let subbed_ctor_result_args =
                    self.sub_ops().apply_sub_to_args(ctor.result_args, &sub);
                self.sub_ops().apply_sub_to_args_in_place(inferred_data_args, &sub);
                Ok((inferred_data_args, subbed_ctor_params, subbed_ctor_result_args))
            })?;

        // Infer the constructor arguments from the term, using the substituted
        // parameters. Substitute any results to the constructor arguments, the
        // result arguments of the constructor, and the constructor data
        // arguments.
        let (final_result_args, resulting_sub, binds) =
            self.infer_args(term.ctor_args, subbed_ctor_params, |inferred_term_ctor_args| {
                let ctor_sub = self.sub_ops().create_sub_from_current_scope();
                self.sub_ops().apply_sub_to_args_in_place(subbed_ctor_result_args, &ctor_sub);
                self.sub_ops().apply_sub_to_args_in_place(inferred_term_ctor_args, &ctor_sub);
                self.sub_ops().apply_sub_to_args_in_place(inferred_ctor_data_args, &ctor_sub);

                // These arguments might have been updated so we need to set them
                term.data_args = inferred_ctor_data_args;
                term.ctor_args = inferred_term_ctor_args;
                original_term_id.set(original_term_id.value().with_data(term.into()));

                // We are exiting the constructor scope, so we need to hide the binds
                let hidden_ctor_sub =
                    self.sub_ops().hide_param_binds(ctor.params.iter(), &ctor_sub);
                Ok((subbed_ctor_result_args, hidden_ctor_sub, HashSet::new()))
            })?;

        // Set the annotation data type to the final result arguments, and unify
        // the annotation type with the expected type.
        annotation_data_ty.args = final_result_args;
        let expected_data_ty =
            Ty::expect_is(original_atom, Ty::from(annotation_data_ty, annotation_ty.origin()));
        let uni_ops = self.uni_ops();
        uni_ops.with_binds(binds);
        uni_ops.add_unification_from_sub(&resulting_sub);
        uni_ops.unify_terms(expected_data_ty, annotation_ty)?;

        // Now we gather the final substitution, and apply it to the result
        // arguments, the constructor data arguments, and finally the annotation
        // type.
        let final_sub = self.sub_ops().create_sub_from_current_scope();
        self.sub_ops().apply_sub_to_args_in_place(subbed_ctor_result_args, &final_sub);
        self.sub_ops().apply_sub_to_args_in_place(inferred_ctor_data_args, &final_sub);
        // Set data args because they might have been updated again
        term.data_args = inferred_ctor_data_args;
        original_term_id.set(original_term_id.value().with_data(term.into()));
        self.sub_ops().apply_sub_to_term_in_place(annotation_ty, &final_sub);

        for (data_arg, result_data_arg) in term.data_args.iter().zip(subbed_ctor_result_args.iter())
        {
            let data_arg = data_arg.value();
            let result_data_arg = result_data_arg.value();
            if let Ty::Hole(_) = *data_arg.value.value() {
                data_arg.value.set(result_data_arg.value.value());
            }
        }

        Ok(())
    }

    /// Potentially run an expression at compile-time.
    ///
    /// This is only done if the expression has a `#run` annotation.
    pub fn potentially_run_expr(&self, expr: TermId, term_ty: TyId) -> TcResult<()> {
        if self.should_monomorphise() {
            let has_run_directive = if let Some(id) = expr.node_id() {
                attr_store().node_has_attr(id, attrs::RUN)
            } else {
                false
            };

            if has_run_directive {
                let norm_ops = self.norm_ops();
                norm_ops.with_mode(NormalisationMode::Full);
                if norm_ops.normalise_in_place(expr.into())? {
                    self.infer_term(expr, term_ty)?;
                }
            }
        }
        Ok(())
    }

    /// Potentially monomorphise a function call, if it is pure.
    pub fn potentially_monomorphise_fn_call(
        &self,
        fn_call: TermId,
        fn_ty: FnTy,
        fn_call_result_ty: TyId,
    ) -> TcResult<()> {
        if self.should_monomorphise() && fn_ty.pure {
            let norm_ops = self.norm_ops();
            norm_ops.with_mode(NormalisationMode::Full);
            if norm_ops.normalise_in_place(fn_call.into())? {
                self.infer_term(fn_call, fn_call_result_ty)?;
            }
        }
        Ok(())
    }

    /// Infer the type of a function call.
    pub fn infer_fn_call_term(
        &self,
        fn_call_term: &CallTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        self.context().enter_scope(ScopeKind::Sub, || {
            self.normalise_and_check_ty(annotation_ty)?;
            let inferred_subject_ty = Ty::hole_for(fn_call_term.subject);
            self.infer_term(fn_call_term.subject, inferred_subject_ty)?;

            match *inferred_subject_ty.value() {
                Ty::FnTy(fn_ty) => {
                    // Potentially fill-in implicit args
                    if let Ty::FnTy(_) = *fn_ty.return_ty.value() && fn_ty.implicit && !fn_call_term.implicit {
                        let applied_args = Arg::seq_from_params_as_holes(fn_ty.params);
                        let copied_subject = Term::inherited_from(fn_call_term.subject, *fn_call_term.subject.value());
                        let new_subject = CallTerm {
                            args: applied_args,
                            subject: copied_subject,
                            implicit: fn_ty.implicit,
                        };
                        fn_call_term.subject.set(fn_call_term.subject.value().with_data(new_subject.into()));
                        return self.infer_fn_call_term(fn_call_term, annotation_ty, original_term_id);
                    }

                    // Check that the function call is of the correct kind.
                    if fn_ty.implicit != fn_call_term.implicit {
                        return Err(TcError::WrongCallKind {
                            site: original_term_id,
                            expected_implicit: fn_ty.implicit,
                            actual_implicit: fn_call_term.implicit,
                        });
                    }

                    let copied_params = self.sub_ops().copy_params(fn_ty.params);
                    let copied_return_ty = self.sub_ops().copy_term(fn_ty.return_ty);

                    let mut fn_call_term = *fn_call_term;
                    self.infer_args(fn_call_term.args, copied_params, |inferred_fn_call_args| {
                        fn_call_term.args = inferred_fn_call_args;
                        original_term_id.set(original_term_id.value().with_data(fn_call_term.into()));

                        self.sub_ops().apply_sub_to_atom_from_context(copied_return_ty);
                        self.check_by_unify(copied_return_ty, annotation_ty)?;
                        Ok(())
                    })?;

                    self.sub_ops().apply_sub_to_atom_from_context(fn_call_term.subject);
                    self.potentially_monomorphise_fn_call(original_term_id, fn_ty, annotation_ty)?;

                    Ok(())
                }
                _ => {
                    // Not a function type.
                    Err(TcError::WrongTy {
                        kind: WrongTermKind::NotAFunction,
                        inferred_term_ty: inferred_subject_ty,
                        term: original_term_id,
                    })
                }
            }
        })
    }

    /// Flag the given function as an entry point if it is one.
    ///
    /// This is done by checking if the function is named "main" or if it has
    /// the #entry_point directive.
    pub fn potentially_flag_fn_as_entry_point(&self, fn_def_id: FnDefId) -> TcResult<()> {
        if self.entry_point().has() {
            return Ok(());
        }

        let fn_def_symbol = fn_def_id.borrow().name;
        let fn_def_name = fn_def_symbol.borrow().name.unwrap();

        // check if on item if it has `entry_point`
        let has_entry_point_attr =
            attr_store().node_has_attr(fn_def_id.node_id_or_default(), attrs::ENTRY_POINT);

        let kind = self.current_source_info().source_id().module_kind();

        let entry_point = if has_entry_point_attr {
            Some(EntryPointKind::Named(fn_def_name))
        } else if fn_def_name == IDENTS.main && kind == Some(ModuleKind::EntryPoint) {
            Some(EntryPointKind::Main)
        } else {
            None
        };

        if let Some(entry_point) = entry_point {
            // @@MissingOrigin
            // Maybe it is better to check this manually?
            let call_term = Node::create_at(
                Term::Call(CallTerm {
                    subject: Node::create_at(Term::Fn(fn_def_id), NodeOrigin::Generated),
                    implicit: false,
                    args: Node::create_at(Node::<Arg>::empty_seq(), NodeOrigin::Generated),
                }),
                NodeOrigin::Generated,
            );

            self.infer_term(call_term, Ty::hole_for(call_term))?;

            // If successful, flag it as an entry point.
            self.entry_point().set(fn_def_id, entry_point);
        }

        Ok(())
    }

    /// Infer the annotation type of a function definition.
    pub fn infer_fn_annotation_ty(
        &self,
        fn_def_id: FnDefId,
        annotation_ty: TyId,
    ) -> TcResult<FnTy> {
        let fn_def = fn_def_id.value();
        let fn_ty = Ty::from(fn_def.ty, fn_def_id.origin());
        self.infer_term(annotation_ty, Ty::universe_of(annotation_ty))?;
        self.infer_term(fn_ty, Ty::universe_of(fn_ty))?;
        self.uni_ops().unify_terms(fn_ty, annotation_ty)?;

        let fn_ty_value = term_as_variant!(self, fn_ty.value(), FnTy);
        fn_def_id.borrow_mut().ty = fn_ty_value;

        Ok(fn_ty_value)
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
    ) -> TcResult<()> {
        self.check_ty(annotation_ty)?;
        if let Some(fn_ty) = self.try_get_inferred_ty(fn_def_id) {
            let expected =
                Ty::expect_is(original_term_id, Ty::from(fn_ty, fn_def_id.origin().inferred()));
            self.check_by_unify(expected, annotation_ty)?;
            return Ok(());
        }

        self.infer_fn_annotation_ty(fn_def_id, annotation_ty)?;
        let fn_def = fn_def_id.value();

        if fn_mode == FnInferMode::Header {
            // If we are only inferring the header, then we also want to check for
            // immediate body functions.
            self.infer_params(fn_def.ty.params, || {
                self.infer_term(fn_def.ty.return_ty, Ty::universe_of(fn_def.ty.return_ty))?;
                if let Term::Fn(immediate_body_fn) = *fn_def.body.value() {
                    self.infer_fn_def(
                        immediate_body_fn,
                        Ty::hole_for(fn_def.body),
                        fn_def.body,
                        FnInferMode::Header,
                    )?;
                }
                Ok(())
            })?;
            return Ok(());
        }

        if self.atom_is_registered(fn_def_id) {
            // Recursive call
            return Ok(());
        }

        self.register_new_atom(fn_def_id, fn_def.ty);

        let fn_def = fn_def_id.value();

        self.context().enter_scope(ScopeKind::Fn(fn_def_id), || {
            self.infer_params(fn_def.ty.params, || {
                self.infer_term(fn_def.ty.return_ty, Ty::universe_of(fn_def.ty.return_ty))?;
                self.infer_term(fn_def.body, fn_def.ty.return_ty)
            })
        })?;

        let fn_ty_id =
            Ty::expect_is(original_term_id, Ty::from(fn_def.ty, fn_def_id.origin().inferred()));
        self.check_by_unify(fn_ty_id, annotation_ty)?;

        self.register_atom_inference(fn_def_id, fn_def_id, fn_def.ty);

        Ok(())
    }

    /// Infer the type of a variable, and return it.
    pub fn infer_var(&self, term: SymbolId, annotation_ty: TyId) -> TcResult<()> {
        match self.context().try_get_decl(term) {
            Some(decl) => {
                if let Some(ty) = decl.ty {
                    let ty = self.sub_ops().copy_term(ty);
                    self.check_ty(ty)?;
                    self.uni_ops().unify_terms(ty, annotation_ty)?;
                    Ok(())
                } else if decl.value.is_some() {
                    panic!("no type found for decl '{}'", decl)
                } else {
                    panic!("Found declaration without type or value during inference: {}", decl)
                }
            }
            None => {
                panic!("no binding found for symbol '{}'", term)
            }
        }
    }

    /// Infer the type of a `return` term, and return it.
    pub fn infer_return_term(
        &self,
        return_term: &ReturnTerm,
        annotation_ty: TyId,
        original_term: TermId,
    ) -> TcResult<()> {
        let closest_fn_def = self.context().get_first_fn_def_in_scope();
        match closest_fn_def {
            Some(closest_fn_def) => {
                // Get the closest fn def in scope, and unify the
                // inferred expression type with its return type.
                // If successful, modify the fn def to set the return type to the inferred type.
                let closest_fn_def_return_ty = closest_fn_def.borrow().ty.return_ty;
                self.infer_term(return_term.expression, closest_fn_def_return_ty)?;

                let inferred_ty = Ty::expect_is(original_term, never_ty(NodeOrigin::Expected));
                self.check_by_unify(inferred_ty, annotation_ty)?;
                Ok(())
            }
            None => panic!("no fn def found in scope for return term"),
        }
    }

    /// Infer the type of a deref term, and return it.
    pub fn infer_deref_term(&self, deref_term: &DerefTerm, annotation_ty: TyId) -> TcResult<()> {
        let deref_inner_inferred = Ty::hole_for(deref_term.subject);
        self.infer_term(deref_term.subject, deref_inner_inferred)?;

        let dereferenced_ty = match *deref_inner_inferred.value() {
            Ty::RefTy(ref_ty) => ref_ty.ty,
            _ => {
                return Err(TcError::CannotDeref {
                    subject: deref_term.subject,
                    actual_subject_ty: deref_inner_inferred,
                })
            }
        };

        self.check_by_unify(dereferenced_ty, annotation_ty)?;
        Ok(())
    }

    /// Infer the type of a loop control term, and return it.
    pub fn infer_loop_control_term(
        &self,
        _: &LoopControlTerm,
        annotation_ty: TyId,
    ) -> TcResult<()> {
        // Always `never`.
        self.check_by_unify(never_ty(NodeOrigin::Expected), annotation_ty)
    }

    /// Infer the type of an unsafe term, and return it.
    pub fn infer_unsafe_term(&self, unsafe_term: &UnsafeTerm, annotation_ty: TyId) -> TcResult<()> {
        // @@Todo: unsafe context
        self.infer_term(unsafe_term.inner, annotation_ty)?;
        Ok(())
    }

    /// Infer the type of a loop term, and return it.
    pub fn infer_loop_term(
        &self,
        loop_term: &LoopTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        // Forward to the inner term.
        self.infer_term(loop_term.inner, Ty::hole(loop_term.inner.origin().inferred()))?;
        let loop_term =
            Ty::expect_is(original_term_id, Ty::unit_ty(original_term_id.origin().inferred()));
        self.check_by_unify(loop_term, annotation_ty)?;
        Ok(())
    }

    /// Infer the type of a block term, and return it.
    pub fn infer_block_term(
        &self,
        block_term: &BlockTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        self.context().enter_scope(block_term.stack_id.into(), || {
            // Handle local mod def
            let stack = block_term.stack_id.value();
            if let Some(local_mod_def) = stack.local_mod_def {
                // @@Improvement: it would be nice to pass through local
                // mod defs in two stages as well.
                self.infer_mod_def(local_mod_def, FnInferMode::Body)?;
            }

            // Keep track of statements diverging, so we can infer the appropriate return
            // type.
            let mut diverges = false;

            for statement in block_term.statements.iter() {
                let ty_to_check_divergence = match *statement.value() {
                    BlockStatement::Decl(decl) => {
                        self.check_ty(decl.ty)?;
                        if let Some(value) = decl.value {
                            self.infer_term(value, decl.ty)?;
                        };
                        self.infer_pat(decl.bind_pat, decl.ty, decl.value)?;

                        // Check that the binding pattern of the declaration is irrefutable.
                        let eck = self.exhaustiveness_checker(decl.bind_pat);
                        eck.is_pat_irrefutable(&[decl.bind_pat], decl.ty, None);
                        self.append_exhaustiveness_diagnostics(eck);

                        decl.ty
                    }
                    BlockStatement::Expr(expr) => {
                        let statement_ty = Ty::hole_for(expr);
                        self.infer_term(expr, statement_ty)?;
                        statement_ty
                    }
                };

                // If the statement diverges, we can already exit
                if self.uni_ops().is_uninhabitable(ty_to_check_divergence)? {
                    diverges = true;
                }
            }

            if diverges {
                match *annotation_ty.value() {
                    Ty::Hole(_) => {
                        // If it diverges, we can just infer the return type as `never`.
                        let block_term_ty =
                            Ty::expect_is(original_term_id, never_ty(NodeOrigin::Expected));
                        self.check_by_unify(block_term_ty, annotation_ty)?;
                    }
                    _ => {
                        // Infer the return value
                        let return_value_ty = Ty::hole_for(block_term.expr);
                        self.infer_term(block_term.expr, return_value_ty)?;
                    }
                }
            } else {
                // Infer the return value
                self.infer_term(block_term.expr, annotation_ty)?;
            };

            let sub = self.sub_ops().create_sub_from_current_scope();
            self.sub_ops().apply_sub_to_term_in_place(annotation_ty, &sub);

            let sub_ops = self.sub_ops();
            let vars_in_scope = sub_ops.get_unassigned_vars_in_current_scope();
            if sub_ops.atom_contains_vars(annotation_ty.into(), &vars_in_scope) {
                return Err(TcError::TryingToReferenceLocalsInType { ty: annotation_ty });
            }

            Ok(())
        })
    }

    /// Infer a `typeof` term, and return it.
    pub fn infer_ty_of_term(
        &self,
        ty_of_term: TyOfTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        let inferred_ty = Ty::hole_for(ty_of_term.term);
        self.infer_term(ty_of_term.term, inferred_ty)?;
        self.infer_term(inferred_ty, annotation_ty)?;
        self.norm_ops().normalise_in_place(original_term_id.into())?;
        Ok(())
    }

    /// Infer a reference term, and return its type.
    pub fn infer_ref_term(
        &self,
        ref_term: &RefTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;
        let annotation_ref_ty = match *annotation_ty.value() {
            Ty::RefTy(ref_ty) => ref_ty,
            Ty::Hole(_) => RefTy {
                kind: ref_term.kind,
                mutable: ref_term.mutable,
                ty: Ty::hole_for(ref_term.subject),
            },
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: Ty::from(
                        RefTy {
                            kind: ref_term.kind,
                            mutable: ref_term.mutable,
                            ty: Ty::hole(ref_term.subject.origin().inferred()),
                        },
                        original_term_id.origin().inferred(),
                    ),
                })
            }
        };

        self.infer_term(ref_term.subject, annotation_ref_ty.ty)?;

        let ty =
            Ty::expect_is(original_term_id, Ty::from(annotation_ref_ty, annotation_ty.origin()));
        self.check_by_unify(ty, annotation_ty)?;
        Ok(())
    }

    /// Infer a cast term, and return its type.
    pub fn infer_cast_term(&self, cast_term: CastTerm, annotation_ty: TyId) -> TcResult<()> {
        self.infer_term(cast_term.subject_term, cast_term.target_ty)?;
        self.check_by_unify(cast_term.target_ty, annotation_ty)?;
        Ok(())
    }

    /// Infer an intrinsic term, and return it.
    pub fn infer_intrinsic(&self, intrinsic: Intrinsic, annotation_ty: TyId) -> TcResult<()> {
        // ##GeneratedOrigin: intrinsics do not belong to the source code
        self.check_by_unify(Term::from(intrinsic.ty(), NodeOrigin::Generated), annotation_ty)?;
        Ok(())
    }

    /// Infer an access term.
    pub fn infer_access_term(
        &self,
        access_term: &AccessTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        let subject_ty = Ty::hole_for(access_term.subject);
        self.infer_term(access_term.subject, subject_ty)?;

        let params = match *subject_ty.value() {
            Ty::TupleTy(tuple_ty) => tuple_ty.data,
            Ty::DataTy(data_ty) => {
                match data_ty.data_def.borrow().get_single_ctor() {
                    Some(ctor) => {
                        let ctor = ctor.value();
                        let data_def = data_ty.data_def.value();
                        let sub = self
                            .sub_ops()
                            .create_sub_from_args_of_params(data_ty.args, data_def.params);
                        self.sub_ops().apply_sub_to_params(ctor.params, &sub)
                    }
                    None => {
                        // Not a record type because it has more than one constructor
                        // @@ErrorReporting: more information about the error
                        return Err(TcError::WrongTy {
                            kind: WrongTermKind::NotARecord,
                            inferred_term_ty: subject_ty,
                            term: original_term_id,
                        });
                    }
                }
            }

            // Not a record type.
            _ => {
                return Err(TcError::WrongTy {
                    kind: WrongTermKind::NotARecord,
                    inferred_term_ty: subject_ty,
                    term: original_term_id,
                })
            }
        };

        if let Some(param) = params.at_index(access_term.field) {
            // Create a substitution that maps the parameters of the record
            // type to the corresponding fields of the record term.
            //
            // i.e. `x: (T: Type, t: T);  x.t: x.T`
            let param_access_sub =
                self.sub_ops().create_sub_from_param_access(params, access_term.subject);
            let subbed_param_ty =
                self.sub_ops().apply_sub_to_term(param.borrow().ty, &param_access_sub);
            self.check_by_unify(subbed_param_ty, annotation_ty)?;
            Ok(())
        } else {
            Err(TcError::PropertyNotFound {
                term: access_term.subject,
                term_ty: subject_ty,
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
    ) -> TcResult<()> {
        self.check_ty(annotation_ty)?;

        let subject_ty = Ty::hole_for(index_term.subject);
        self.infer_term(index_term.subject, subject_ty)?;
        self.normalise_and_check_ty(subject_ty)?;

        // Ensure the index is a usize
        let index_ty =
            Ty::expect_is(index_term.index, usize_ty(index_term.index.origin().inferred()));
        self.infer_term(index_term.index, index_ty)?;

        let wrong_subject_ty = || {
            Err(TcError::WrongTy {
                term: original_term_id,
                inferred_term_ty: subject_ty,
                kind: WrongTermKind::NotAnArray,
            })
        };

        // Ensure that the subject is array-like
        let inferred_ty = match *subject_ty.value() {
            Ty::DataTy(data_ty) => {
                let data_def = data_ty.data_def.value();
                if let DataDefCtors::Primitive(PrimitiveCtorInfo::Array(array_primitive)) =
                    data_def.ctors
                {
                    let sub = self
                        .sub_ops()
                        .create_sub_from_args_of_params(data_ty.args, data_def.params);
                    let array_ty =
                        self.sub_ops().apply_sub_to_term(array_primitive.element_ty, &sub);
                    Ok(array_ty)
                } else {
                    wrong_subject_ty()
                }
            }
            _ => wrong_subject_ty(),
        }?;

        self.check_by_unify(inferred_ty, annotation_ty)?;
        Ok(())
    }

    /// Infer an assign term.
    pub fn infer_assign_term(
        &self,
        assign_term: &AssignTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        let subject_ty = Ty::hole_for(assign_term.subject);
        self.infer_term(assign_term.subject, subject_ty)?;

        let value_ty = Ty::hole_for(assign_term.value);
        self.infer_term(assign_term.value, value_ty)?;

        self.check_by_unify(value_ty, subject_ty)?;

        let inferred_ty =
            Ty::expect_is(original_term_id, Ty::unit_ty(original_term_id.origin().inferred()));
        self.check_by_unify(inferred_ty, annotation_ty)?;
        Ok(())
    }

    /// Infer a match term.
    pub fn infer_match_term(&self, match_term: &MatchTerm, annotation_ty: TyId) -> TcResult<()> {
        self.check_ty(annotation_ty)?;
        let match_subject_ty = Ty::hole_for(match_term.subject);
        self.infer_term(match_term.subject, match_subject_ty)?;

        let match_subject_var = match *match_term.subject.value() {
            Term::Var(v) => Some(v),
            _ => None,
        };

        let match_annotation_ty = match *annotation_ty.value() {
            Ty::Hole(_) => None,
            t => Some(t),
        };

        let mut unified_ty = annotation_ty;
        let inhabited = Cell::new(false);
        for case in match_term.cases.iter() {
            let case_data = case.value();
            self.context().enter_scope(case_data.stack_id.into(), || -> TcResult<_> {
                let subject_ty_copy = self.sub_ops().copy_term(match_subject_ty);

                self.infer_pat(case_data.bind_pat, subject_ty_copy, Some(match_term.subject))?;
                let new_unified_ty =
                    Ty::expect_is(case_data.value, self.sub_ops().copy_term(unified_ty));

                if let Some(match_subject_var) = match_subject_var {
                    if let Some(pat_term) = self.try_use_pat_as_term(case_data.bind_pat) {
                        self.context().add_assignment(match_subject_var, subject_ty_copy, pat_term);
                    }
                }

                match match_annotation_ty {
                    _ if self.uni_ops().is_uninhabitable(subject_ty_copy)? => {
                        let new_unified_ty = Ty::hole_for(case_data.value);
                        self.infer_term(case_data.value, new_unified_ty)?;
                        self.check_by_unify(new_unified_ty, never_ty(NodeOrigin::Expected))?;
                    }
                    Some(_) => {
                        self.infer_term(case_data.value, new_unified_ty)?;
                        if !self.uni_ops().is_uninhabitable(new_unified_ty)? {
                            inhabited.set(true);
                        }
                    }
                    None => {
                        self.infer_term(case_data.value, new_unified_ty)?;
                        if !self.uni_ops().is_uninhabitable(new_unified_ty)? {
                            inhabited.set(true);
                            self.uni_ops().unify_terms(new_unified_ty, unified_ty)?;
                            unified_ty = new_unified_ty;
                        }
                    }
                }

                Ok(())
            })?
        }

        if matches!(*unified_ty.value(), Ty::Hole(_)) {
            if !inhabited.get() {
                unified_ty = never_ty(NodeOrigin::Expected);
            } else {
                unified_ty = Ty::unit_ty(NodeOrigin::Expected);
            }
        }

        self.check_by_unify(unified_ty, annotation_ty)?;

        // @@Caching: Check if the MatchTerm has already been queued for exhaustiveness,
        // if it hasn't, we can use/make a new ExhaustivenessChecker and then
        // add the job.
        let pats =
            match_term.cases.elements().borrow().iter().map(|case| case.bind_pat).collect_vec();
        let eck = self.exhaustiveness_checker(match_term.subject);
        eck.is_match_exhaustive(&pats, match_subject_ty);
        self.append_exhaustiveness_diagnostics(eck);

        Ok(())
    }

    /// Infer a concrete type for a given term.
    ///
    /// If this is not possible, return `None`.
    /// To create a hole when this is not possible, use
    /// [`InferOps::infer_term_of_term_or_hole`].
    pub fn infer_term(&self, term_id: TermId, annotation_ty: TyId) -> TcResult<()> {
        self.register_new_atom(term_id, annotation_ty);
        let expects_ty = |ty: TyId| self.check_by_unify(ty, Ty::universe(NodeOrigin::Expected));

        match *term_id.value() {
            Term::Tuple(tuple_term) => {
                self.infer_tuple_term(&tuple_term, annotation_ty, term_id)?
            }
            Term::Lit(lit_term) => self.infer_lit(lit_term, annotation_ty)?,
            Term::Array(prim_term) => self.infer_array_term(&prim_term, annotation_ty)?,
            Term::Ctor(ctor_term) => self.infer_ctor_term(&ctor_term, annotation_ty, term_id)?,
            Term::Call(fn_call_term) => {
                self.infer_fn_call_term(&fn_call_term, annotation_ty, term_id)?
            }
            Term::Fn(fn_def_id) => {
                self.infer_fn_def(fn_def_id, annotation_ty, term_id, FnInferMode::Body)?
            }
            Term::Var(var_term) => self.infer_var(var_term, annotation_ty)?,
            Term::Return(return_term) => {
                self.infer_return_term(&return_term, annotation_ty, term_id)?
            }
            Term::Deref(deref_term) => self.infer_deref_term(&deref_term, annotation_ty)?,
            Term::LoopControl(loop_control_term) => {
                self.infer_loop_control_term(&loop_control_term, annotation_ty)?
            }
            Term::Unsafe(unsafe_term) => self.infer_unsafe_term(&unsafe_term, annotation_ty)?,
            Term::Loop(loop_term) => self.infer_loop_term(&loop_term, annotation_ty, term_id)?,
            Term::Block(block_term) => {
                self.infer_block_term(&block_term, annotation_ty, term_id)?
            }
            Term::TypeOf(ty_of_term) => {
                self.infer_ty_of_term(ty_of_term, annotation_ty, term_id)?
            }
            Term::Ref(ref_term) => self.infer_ref_term(&ref_term, annotation_ty, term_id)?,
            Term::Cast(cast_term) => self.infer_cast_term(cast_term, annotation_ty)?,
            Term::Access(access_term) => {
                self.infer_access_term(&access_term, annotation_ty, term_id)?
            }
            Term::Index(index_term) => {
                self.infer_index_term(&index_term, annotation_ty, term_id)?
            }
            Term::Match(match_term) => self.infer_match_term(&match_term, annotation_ty)?,
            Term::Assign(assign_term) => {
                self.infer_assign_term(&assign_term, annotation_ty, term_id)?
            }
            Term::Intrinsic(intrinsic) => self.infer_intrinsic(intrinsic, annotation_ty)?,
            Term::Hole(_) => {}
            Ty::TupleTy(tuple_ty) => {
                self.infer_params(tuple_ty.data, || Ok(()))?;
                expects_ty(annotation_ty)?;
            }
            Ty::FnTy(fn_ty) => {
                self.infer_params(fn_ty.params, || {
                    self.infer_term(fn_ty.return_ty, Ty::universe(NodeOrigin::Expected))
                })?;
                expects_ty(annotation_ty)?;
            }
            Ty::RefTy(ref_ty) => {
                // Infer the inner type
                self.infer_term(ref_ty.ty, Ty::universe(NodeOrigin::Expected))?;
                expects_ty(annotation_ty)?;
            }
            Ty::DataTy(mut data_ty) => {
                let data_def = data_ty.data_def.value();
                let copied_params = self.sub_ops().copy_params(data_def.params);
                self.infer_args(data_ty.args, copied_params, |inferred_data_ty_args| {
                    data_ty.args = inferred_data_ty_args;
                    term_id.set(term_id.value().with_data(data_ty.into()));
                    Ok(())
                })?;
                expects_ty(annotation_ty)?;
            }
            Ty::Universe => {
                expects_ty(annotation_ty)?;
            }
        };

        self.check_ty(annotation_ty)?;
        self.register_atom_inference(term_id, term_id, annotation_ty);

        // Potentially evaluate the term.
        self.potentially_run_expr(term_id, annotation_ty)?;
        self.potentially_dump_tir(term_id);

        Ok(())
    }

    /// Infer a range pattern.
    pub fn infer_range_pat(&self, range_pat: RangePat, annotation_ty: TyId) -> TcResult<()> {
        let RangePat { lo, hi, .. } = range_pat;

        lo.map(|lo| self.infer_lit(*lo, annotation_ty)).transpose()?;
        hi.map(|hi| self.infer_lit(*hi, annotation_ty)).transpose()?;

        Ok(())
    }

    /// Infer a tuple pattern.
    pub fn infer_tuple_pat(
        &self,
        tuple_pat: &TuplePat,
        annotation_ty: TyId,
        original_pat_id: PatId,
    ) -> TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;
        let params = match *annotation_ty.value() {
            Ty::TupleTy(tuple_ty) => tuple_ty.data,
            Ty::Hole(_) => Param::seq_from_args_with_hole_types(tuple_pat.data),
            _ => {
                let inferred = Param::seq_from_args_with_hole_types(tuple_pat.data);
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: Ty::expect_is(
                        original_pat_id,
                        Ty::from(TupleTy { data: inferred }, original_pat_id.origin().inferred()),
                    ),
                });
            }
        };
        let mut tuple_pat = *tuple_pat;
        self.infer_pat_args(tuple_pat.data, tuple_pat.data_spread, params, |new_args| {
            tuple_pat.data = new_args;
            original_pat_id.set(original_pat_id.value().with_data(tuple_pat.into()));
            Ok(())
        })?;

        let tuple_ty = Ty::expect_is(
            original_pat_id,
            Ty::from(TupleTy { data: params }, annotation_ty.origin()),
        );
        self.check_by_unify(tuple_ty, annotation_ty)?;
        Ok(())
    }

    /// Infer a list pattern
    pub fn infer_array_pat(
        &self,
        list_pat: &ArrayPat,
        annotation_ty: TyId,
        original_pat_id: PatId,
    ) -> TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;
        // @@Todo: `use_ty_as_array` instead of this manual match:
        let list_annotation_inner_ty = match *annotation_ty.value() {
            Ty::DataTy(data) if data.data_def == list_def() => {
                // Type is already checked
                assert!(data.args.len() == 1);

                ArgId(data.args.elements(), 0).borrow().value
            }
            Ty::Hole(_) => Ty::hole(list_pat.pats.origin()),
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: list_ty(
                        Ty::hole(NodeOrigin::Generated),
                        original_pat_id.origin().inferred(),
                    ),
                });
            }
        };

        self.infer_unified_pat_list(list_pat.pats, list_annotation_inner_ty)?;
        let list_ty = list_ty(list_annotation_inner_ty, NodeOrigin::Expected);
        self.check_by_unify(list_ty, annotation_ty)?;
        Ok(())
    }

    /// Infer a constructor pattern
    pub fn infer_ctor_pat(
        &self,
        pat: &CtorPat,
        annotation_ty: TyId,
        original_pat_id: PatId,
    ) -> TcResult<()> {
        let mut pat = *pat;
        let ctor_def_id = pat.ctor;
        let data_args = pat.data_args;
        let original_atom: Atom = original_pat_id.into();
        let ctor = ctor_def_id.value();
        let data_def = ctor.data_def_id.value();

        // Ensure the annotation is valid
        self.normalise_and_check_ty(annotation_ty)?;

        // Get the annotation as a DataTy, or create a hole one if not given
        let mut annotation_data_ty = match *annotation_ty.value() {
            Ty::DataTy(data) if data.data_def == ctor.data_def_id => DataTy {
                data_def: ctor.data_def_id,
                args: if data.args.len() == 0 {
                    Arg::seq_from_params_as_holes(data_def.params)
                } else {
                    data.args
                },
            },
            Ty::Hole(_) => DataTy {
                data_def: ctor.data_def_id,
                args: Arg::seq_from_params_as_holes(data_def.params),
            },
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: Ty::from(
                        DataTy { args: data_args, data_def: ctor.data_def_id },
                        original_atom.origin().inferred(),
                    ),
                });
            }
        };

        // Get the data arguments given to the constructor, like Equal<...>::Refl(...)
        //                                                             ^^^ these
        let ctor_data_args = if data_args.len() == 0 {
            Arg::seq_from_params_as_holes(data_def.params)
        } else {
            data_args
        };

        // From the given constructor data args, substitute the constructor params and
        // result arguments. In the process, infer the data args more if
        // possible.
        let copied_params = self.sub_ops().copy_params(data_def.params);
        let (inferred_ctor_data_args, subbed_ctor_params, subbed_ctor_result_args) = self
            .infer_args(ctor_data_args, copied_params, |inferred_data_args| {
                let sub = self.sub_ops().create_sub_from_current_scope();
                let subbed_ctor_params = self.sub_ops().apply_sub_to_params(ctor.params, &sub);
                let subbed_ctor_result_args =
                    self.sub_ops().apply_sub_to_args(ctor.result_args, &sub);
                self.sub_ops().apply_sub_to_args_in_place(inferred_data_args, &sub);
                Ok((inferred_data_args, subbed_ctor_params, subbed_ctor_result_args))
            })?;

        // Infer the constructor arguments from the term, using the substituted
        // parameters. Substitute any results to the constructor arguments, the
        // result arguments of the constructor, and the constructor data
        // arguments.
        let (final_result_args, resulting_sub, binds) = self.infer_pat_args(
            pat.ctor_pat_args,
            pat.ctor_pat_args_spread,
            subbed_ctor_params,
            |inferred_pat_ctor_args| {
                let ctor_sub = self.sub_ops().create_sub_from_current_scope();
                self.sub_ops().apply_sub_to_args_in_place(subbed_ctor_result_args, &ctor_sub);
                self.sub_ops().apply_sub_to_pat_args_in_place(inferred_pat_ctor_args, &ctor_sub);
                self.sub_ops().apply_sub_to_args_in_place(inferred_ctor_data_args, &ctor_sub);

                // These arguments might have been updated so we need to set them
                pat.data_args = inferred_ctor_data_args;
                pat.ctor_pat_args = inferred_pat_ctor_args;
                original_pat_id.set(original_pat_id.value().with_data(pat.into()));

                // We are exiting the constructor scope, so we need to hide the binds
                let hidden_ctor_sub =
                    self.sub_ops().hide_param_binds(ctor.params.iter(), &ctor_sub);
                Ok((
                    subbed_ctor_result_args,
                    hidden_ctor_sub,
                    self.get_binds_in_pat_args(inferred_pat_ctor_args),
                ))
            },
        )?;

        // Set the annotation data type to the final result arguments, and unify
        // the annotation type with the expected type.
        annotation_data_ty.args = final_result_args;
        let expected_data_ty =
            Ty::expect_is(original_atom, Ty::from(annotation_data_ty, annotation_ty.origin()));
        let uni_ops = self.uni_ops();
        uni_ops.with_binds(binds);
        uni_ops.add_unification_from_sub(&resulting_sub);
        uni_ops.unify_terms(expected_data_ty, annotation_ty)?;

        // Now we gather the final substitution, and apply it to the result
        // arguments, the constructor data arguments, and finally the annotation
        // type.
        let final_sub = self.sub_ops().create_sub_from_current_scope();
        self.sub_ops().apply_sub_to_args_in_place(subbed_ctor_result_args, &final_sub);
        self.sub_ops().apply_sub_to_args_in_place(inferred_ctor_data_args, &final_sub);
        self.sub_ops().apply_sub_to_pat_args_in_place(pat.ctor_pat_args, &final_sub);
        // Set data args because they might have been updated again
        pat.data_args = inferred_ctor_data_args;
        original_pat_id.set(original_pat_id.value().with_data(pat.into()));
        self.sub_ops().apply_sub_to_term_in_place(annotation_ty, &final_sub);

        for (data_arg, result_data_arg) in pat.data_args.iter().zip(subbed_ctor_result_args.iter())
        {
            let data_arg = data_arg.value();
            let result_data_arg = result_data_arg.value();
            if let Ty::Hole(_) = *data_arg.value.value() {
                data_arg.value.set(result_data_arg.value.value());
            }
        }

        Ok(())
    }

    /// Infer an or-pattern
    pub fn infer_or_pat(&self, pat: &OrPat, annotation_ty: TyId) -> TcResult<()> {
        self.infer_unified_pat_list(pat.alternatives, annotation_ty)?;
        Ok(())
    }

    /// Infer an if-pattern
    pub fn infer_if_pat(&self, pat: &IfPat, annotation_ty: TyId) -> TcResult<()> {
        self.infer_pat(pat.pat, annotation_ty, None)?;
        let expected_condition_ty = Ty::expect_is(pat.condition, bool_ty(NodeOrigin::Expected));
        self.infer_term(pat.condition, expected_condition_ty)?;
        if let Term::Var(v) = *pat.condition.value() {
            self.context().add_assignment(
                v,
                expected_condition_ty,
                bool_term(true, pat.condition.origin().inferred()),
            );
        }
        Ok(())
    }

    /// Infer the type of a pattern, and return it.
    pub fn infer_pat(
        &self,
        pat_id: PatId,
        annotation_ty: TyId,
        binds_to: Option<TermId>,
    ) -> TcResult<()> {
        self.register_new_atom(pat_id, annotation_ty);

        match *pat_id.value() {
            Pat::Binding(var) => {
                self.check_ty(annotation_ty)?;
                match binds_to {
                    Some(value)
                        if self.norm_ops().atom_has_effects(value.into()) == Some(false) =>
                    {
                        self.context().add_assignment_to_closest_stack(
                            var.name,
                            annotation_ty,
                            value,
                        );
                    }
                    _ => {
                        self.context().add_typing_to_closest_stack(var.name, annotation_ty);
                    }
                }
            }
            Pat::Range(range_pat) => self.infer_range_pat(range_pat, annotation_ty)?,
            Pat::Lit(lit) => self.infer_lit(*lit, annotation_ty)?,
            Pat::Tuple(tuple_pat) => self.infer_tuple_pat(&tuple_pat, annotation_ty, pat_id)?,
            Pat::Array(list_term) => self.infer_array_pat(&list_term, annotation_ty, pat_id)?,
            Pat::Ctor(ctor_pat) => self.infer_ctor_pat(&ctor_pat, annotation_ty, pat_id)?,
            Pat::Or(or_pat) => self.infer_or_pat(&or_pat, annotation_ty)?,
            Pat::If(if_pat) => self.infer_if_pat(&if_pat, annotation_ty)?,
        };

        self.register_atom_inference(pat_id, pat_id, annotation_ty);
        Ok(())
    }

    /// Infer the given constructor definition.
    pub fn infer_ctor_def(&self, ctor: CtorDefId) -> TcResult<()> {
        let ctor_def = ctor.value();
        self.infer_params(ctor_def.params, || {
            let return_ty = Ty::from(
                DataTy { data_def: ctor_def.data_def_id, args: ctor_def.result_args },
                ctor.origin(),
            );
            self.infer_term(return_ty, Ty::universe_of(return_ty))?;
            Ok(())
        })
    }

    /// Infer the given data definition.
    pub fn infer_data_def(&self, data_def_id: DataDefId) -> TcResult<()> {
        let (data_def_params, data_def_ctors) =
            data_def_id.map(|data_def| (data_def.params, data_def.ctors));

        self.infer_params(data_def_params, || {
            match data_def_ctors {
                DataDefCtors::Defined(data_def_ctors_id) => {
                    let mut error_state = ErrorState::new();

                    // Infer each member
                    for ctor_idx in data_def_ctors_id.value().to_index_range() {
                        let _ = error_state.try_or_add_error(
                            self.infer_ctor_def(CtorDefId(data_def_ctors_id.elements(), ctor_idx)),
                        );
                    }

                    error_state.into_error(|| Ok(()))
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
                            self.infer_term(
                                array_ctor_info.element_ty,
                                Ty::universe_of(array_ctor_info.element_ty),
                            )?;
                            if let Some(length) = array_ctor_info.length {
                                self.infer_term(length, usize_ty(NodeOrigin::Expected))?;
                            }
                            Ok(())
                        }
                    }
                }
            }
        })
    }

    /// Dump the TIR for the given target if it has a `#dump_tir` directive
    /// applied on it.
    pub fn potentially_dump_tir(&self, target: impl ToString + HasAstNodeId) {
        let has_dump_dir = if let Some(id) = target.node_id() {
            attr_store().node_has_attr(id, attrs::DUMP_TIR)
        } else {
            false
        };

        if has_dump_dir {
            dump_tir(target);
        }
    }

    /// Infer the given module member.
    pub fn infer_mod_member(&self, mod_member: ModMemberId, fn_mode: FnInferMode) -> TcResult<()> {
        let value = mod_member.borrow().value;
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
                self.infer_fn_def(
                    fn_def_id,
                    Ty::hole(fn_def_id.origin().inferred()),
                    Term::hole(fn_def_id.origin()),
                    fn_mode,
                )?;
                if fn_mode == FnInferMode::Body {
                    // Dump TIR if necessary
                    self.potentially_dump_tir(fn_def_id);

                    // Check for entry point
                    self.potentially_flag_fn_as_entry_point(fn_def_id)?;
                }
                Ok(())
            }
            ModMemberValue::Intrinsic(_) => {
                // Nothing to do
                Ok(())
            }
        }
    }

    /// Infer the given module definition.
    pub fn infer_mod_def(&self, mod_def_id: ModDefId, fn_mode: FnInferMode) -> TcResult<()> {
        self.context().enter_scope(mod_def_id.into(), || {
            let members = mod_def_id.borrow().members;
            let mut error_state = ErrorState::new();

            // Infer each member signature
            for member_idx in members.value().to_index_range() {
                let _ = error_state.try_or_add_error(
                    self.infer_mod_member(ModMemberId(members.elements(), member_idx), fn_mode),
                );
            }

            error_state.into_error(|| Ok(()))
        })
    }
}
