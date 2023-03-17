//! Operations to infer types of terms and patterns.

use std::{cell::Cell, collections::HashSet, ops::ControlFlow};

use derive_more::{Constructor, Deref};
use hash_ast::ast::{FloatLitKind, IntLitKind};
use hash_intrinsics::utils::PrimitiveUtils;
use hash_source::{
    constant::{FloatTy, IntTy, SIntTy, UIntTy, CONSTANT_MAP},
    entry_point::EntryPointKind,
    identifier::IDENTS,
    ModuleKind,
};
use hash_tir::{
    access::AccessTerm,
    args::{ArgData, ArgsId, PatArgsId, PatOrCapture},
    arrays::{ArrayPat, ArrayTerm, IndexTerm},
    atom_info::ItemInAtomInfo,
    casting::CastTerm,
    control::{IfPat, LoopControlTerm, LoopTerm, MatchTerm, OrPat, ReturnTerm},
    data::{CtorDefId, CtorPat, CtorTerm, DataDefCtors, DataDefId, DataTy, PrimitiveCtorInfo},
    directives::DirectiveTarget,
    environment::{
        context::{BindingKind, ScopeKind},
        env::AccessToEnv,
    },
    fns::{FnBody, FnCallTerm, FnDefId, FnTy},
    lits::Lit,
    locations::LocationTarget,
    mods::{ModDefId, ModMemberId, ModMemberValue},
    params::ParamsId,
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
    utils::{common::CommonUtils, traversing::Atom, AccessToUtils},
};
use hash_utils::store::{CloneStore, PartialCloneStore, SequenceStore, SequenceStoreKey, Store};

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
                    let param = self.get_param(param_id);
                    let param_ty = self.sub_ops().copy_ty(param.ty);
                    infer_arg(&arg, param_ty)?;
                    self.sub_ops().apply_sub_to_atom_from_context(param_ty);
                    if let Some(value) = get_arg_value(&arg) {
                        self.context_utils().add_assignment(param.name, param_ty, value);
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
        let terms = self.stores().term_list().get_vec(term_list_id);
        self.infer_unified_list(&terms, element_annotation_ty, |term, ty| {
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
        let pats = self.stores().pat_list().get_vec(pat_list_id);
        self.infer_unified_list(&pats, element_annotation_ty, |pat, ty| match pat {
            PatOrCapture::Pat(pat) => {
                self.infer_pat(pat, ty, None)?;
                Ok(())
            }
            PatOrCapture::Capture => Ok(()),
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
        let reordered_args_id =
            self.param_ops().validate_and_reorder_args_against_params(args, annotation_params)?;

        let result = self.infer_some_args(
            reordered_args_id.iter(),
            annotation_params,
            |arg, param_ty| {
                let arg = self.get_arg(*arg);
                self.infer_term(arg.value, param_ty)?;
                Ok(())
            },
            |arg| {
                let arg = self.get_arg(*arg);
                Some(arg.value)
            },
            || in_arg_scope(reordered_args_id),
        )?;

        Ok(result)
    }

    pub fn try_use_pat_args_as_term_args(&self, pat_args: PatArgsId) -> Option<ArgsId> {
        let mut args = Vec::new();
        for pat_arg in pat_args.iter() {
            let pat_arg = self.get_pat_arg(pat_arg);
            match pat_arg.pat {
                PatOrCapture::Pat(pat) => {
                    let term = self.try_use_pat_as_term(pat)?;
                    args.push(ArgData { target: pat_arg.target, value: term });
                }
                PatOrCapture::Capture => return None,
            }
        }
        Some(self.param_utils().create_args(args.into_iter()))
    }

    pub fn try_use_pat_as_term(&self, pat_id: PatId) -> Option<TermId> {
        match self.get_pat(pat_id) {
            Pat::Binding(var) => Some(self.new_term(var.name)),
            Pat::Range(_) => Some(self.new_term(self.new_fresh_symbol())),
            Pat::Lit(lit) => Some(self.new_term(Term::Lit(lit.into()))),
            Pat::Ctor(ctor_pat) => Some(self.new_term(CtorTerm {
                ctor: ctor_pat.ctor,
                data_args: ctor_pat.data_args,
                ctor_args: self.try_use_pat_args_as_term_args(ctor_pat.ctor_pat_args)?,
            })),
            Pat::Tuple(tuple_pat) => {
                Some(self.new_term(TupleTerm {
                    data: self.try_use_pat_args_as_term_args(tuple_pat.data)?,
                }))
            }
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
        let reordered_pat_args_id = self.param_ops().validate_and_reorder_pat_args_against_params(
            pat_args,
            spread,
            annotation_params,
        )?;

        self.infer_some_args(
            reordered_pat_args_id.iter(),
            annotation_params,
            |pat_arg, param_ty| {
                let pat_arg = self.get_pat_arg(*pat_arg);
                match pat_arg.pat {
                    PatOrCapture::Pat(pat) => {
                        self.infer_pat(pat, param_ty, None)?;
                        Ok(())
                    }
                    PatOrCapture::Capture => Ok(()),
                }
            },
            |arg| {
                let arg = self.get_pat_arg(*arg);
                match arg.pat {
                    PatOrCapture::Pat(pat) => self.try_use_pat_as_term(pat),
                    PatOrCapture::Capture => None,
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
                let param = self.get_param(param_id);
                self.context_utils().add_typing(param.name, param.ty);
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
        self.param_ops().validate_params(params)?;

        let (result, shadowed_sub) =
            self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
                for param_id in params.iter() {
                    let param = self.get_param(param_id);
                    self.infer_ty(param.ty, self.new_flexible_universe_ty())?;
                    self.context_utils().add_typing(param.name, param.ty);
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
        self.uni_ops().unify_tys(inferred_ty, annotation_ty)
    }

    /// Check that the given type is well-formed, and normalise it.
    pub fn check_ty(&self, ty: TyId) -> TcResult<()> {
        match self.get_ty(ty) {
            Ty::Hole(_) => Ok(()),
            _ => self.infer_ty(ty, self.new_flexible_universe_ty()),
        }
    }

    /// Check that the given type is well-formed, and normalise it.
    pub fn normalise_and_check_ty(&self, ty: TyId) -> TcResult<()> {
        match self.get_ty(ty) {
            Ty::Hole(_) => Ok(()),
            _ => {
                self.infer_ty(ty, self.new_flexible_universe_ty())?;
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
        self.normalise_and_check_ty(annotation_ty)?;
        let params = match self.get_ty(annotation_ty) {
            Ty::Tuple(tuple_ty) => self.sub_ops().copy_params(tuple_ty.data),
            Ty::Hole(_) => self.param_utils().create_hole_params_from_args(tuple_term.data),
            _ => {
                let inferred = self.param_utils().create_hole_params_from_args(tuple_term.data);
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: self.new_ty(TupleTy { data: inferred }),
                    inferred_from: Some(original_term_id.into()),
                });
            }
        };

        let mut tuple_term = *tuple_term;
        self.infer_args(tuple_term.data, params, |new_args| {
            tuple_term.data = new_args;
            self.stores().term().set(original_term_id, tuple_term.into());
            Ok(())
        })?;

        let tuple_ty =
            self.new_expected_ty_of(original_term_id, self.new_ty(TupleTy { data: params }));
        self.check_by_unify(tuple_ty, annotation_ty)?;
        Ok(())
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
                        self.env().target().ptr_size(),
                    );
                }
                // @@Incomplete: as above
            }
            _ => {}
        }
        Ok(())
    }

    /// Infer the type of a literal.
    pub fn infer_lit(&self, lit: &Lit, annotation_ty: TyId) -> TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;
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
                        (match self.get_ty(annotation_ty) {
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
                    (match self.get_ty(annotation_ty) {
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
                    .unwrap_or_else(|| self.primitives().f64())
                }
            },
        });

        self.check_by_unify(inferred_ty, annotation_ty)?;
        self.adjust_lit_repr(lit, inferred_ty)?;
        Ok(())
    }

    pub fn use_ty_as_array(
        &self,
        annotation_ty: TyId,
        inferred_from: Option<LocationTarget>,
    ) -> TcResult<Option<(TyId, Option<TermId>)>> {
        let mismatch = || {
            Err(TcError::MismatchingTypes {
                expected: annotation_ty,
                actual: {
                    self.new_expected_ty_of_ty(
                        annotation_ty,
                        self.new_ty(DataTy {
                            data_def: self.primitives().list(),
                            args: self.new_args(&[self.new_term(self.new_ty_hole())]),
                        }),
                    )
                },
                inferred_from,
            })
        };

        match self.get_ty(annotation_ty) {
            Ty::Data(data) => {
                let data_def = self.get_data_def(data.data_def);

                match data_def.ctors {
                    DataDefCtors::Primitive(primitive) => {
                        if let PrimitiveCtorInfo::Array(array_prim) = primitive {
                            // First infer the data arguments
                            let copied_params = self.sub_ops().copy_params(data_def.params);
                            self.infer_args(data.args, copied_params, |_| {
                                let sub = self.sub_ops().create_sub_from_current_scope();
                                let subbed_element_ty =
                                    self.sub_ops().apply_sub_to_ty(array_prim.element_ty, &sub);
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
    pub fn infer_array_term(
        &self,
        array_term: &ArrayTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;
        let (list_annotation_inner_ty, list_len) = self
            .use_ty_as_array(annotation_ty, Some(original_term_id.into()))?
            .unwrap_or_else(|| (self.new_ty_hole(), None));

        self.infer_unified_term_list(array_term.elements, list_annotation_inner_ty)?;

        // Ensure the array lengths match if given
        if let Some(len) = list_len {
            let inferred_len_term = self.create_term_from_integer_lit(array_term.elements.len());
            if !self.uni_ops().terms_are_equal(len, inferred_len_term) {
                return Err(TcError::MismatchingArrayLengths {
                    expected_len: len,
                    got_len: inferred_len_term,
                });
            }
        }

        // Either create a default list type or apply the substitution to the annotation
        // type
        if let Ty::Hole(_) = self.get_ty(annotation_ty) {
            self.check_by_unify(
                self.new_ty(DataTy {
                    data_def: self.primitives().list(),
                    args: self.new_args(&[self.new_term(list_annotation_inner_ty)]),
                }),
                annotation_ty,
            )?
        };

        Ok(())
    }

    pub fn get_binds_in_pat_atom_once(
        &self,
        atom: Atom,
        set: &mut HashSet<Symbol>,
    ) -> ControlFlow<()> {
        if let Atom::Pat(pat_id) = atom {
            match self.get_pat(pat_id) {
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

    pub fn get_binds_in_pat(&self, pat: PatId) -> HashSet<Symbol> {
        let mut binds = HashSet::new();
        self.traversing_utils()
            .visit_pat::<!, _>(pat, &mut |atom| {
                Ok(self.get_binds_in_pat_atom_once(atom, &mut binds))
            })
            .into_ok();
        binds
    }

    pub fn get_binds_in_pat_args(&self, pat_args: PatArgsId) -> HashSet<Symbol> {
        let mut binds = HashSet::new();
        self.traversing_utils()
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
        let ctor = self.get_ctor_def(ctor_def_id);
        let data_def = self.get_data_def(ctor.data_def_id);

        // Ensure the annotation is valid
        self.normalise_and_check_ty(annotation_ty)?;

        // Get the annotation as a DataTy, or create a hole one if not given
        let mut annotation_data_ty = match self.get_ty(annotation_ty) {
            Ty::Data(data) if data.data_def == ctor.data_def_id => DataTy {
                data_def: data_def.id,
                args: if data.args.len() == 0 {
                    self.param_utils().instantiate_params_as_holes(data_def.params)
                } else {
                    data.args
                },
            },
            Ty::Hole(_) => DataTy {
                data_def: data_def.id,
                args: self.param_utils().instantiate_params_as_holes(data_def.params),
            },
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: self.new_ty(DataTy { args: data_args, data_def: ctor.data_def_id }),
                    inferred_from: Some(original_atom.into()),
                });
            }
        };

        // Get the data arguments given to the constructor, like Equal<...>::Refl(...)
        //                                                             ^^^ these
        let ctor_data_args = if data_args.len() == 0 {
            self.param_utils().instantiate_params_as_holes(data_def.params)
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
                self.stores().term().set(original_term_id, term.into());

                // We are exiting the constructor scope, so we need to hide the binds
                let hidden_ctor_sub =
                    self.sub_ops().hide_param_binds(ctor.params.iter(), &ctor_sub);
                Ok((subbed_ctor_result_args, hidden_ctor_sub, HashSet::new()))
            })?;

        // Set the annotation data type to the final result arguments, and unify
        // the annotation type with the expected type.
        annotation_data_ty.args = final_result_args;
        let expected_data_ty =
            self.new_expected_ty_of(original_atom, self.new_ty(annotation_data_ty));
        let uni_ops = self.uni_ops();
        uni_ops.with_binds(binds);
        uni_ops.add_unification_from_sub(&resulting_sub);
        uni_ops.unify_tys(expected_data_ty, annotation_ty)?;

        // Now we gather the final substitution, and apply it to the result
        // arguments, the constructor data arguments, and finally the annotation
        // type.
        let final_sub = self.sub_ops().create_sub_from_current_scope();
        self.sub_ops().apply_sub_to_args_in_place(subbed_ctor_result_args, &final_sub);
        self.sub_ops().apply_sub_to_args_in_place(inferred_ctor_data_args, &final_sub);
        // Set data args because they might have been updated again
        term.data_args = inferred_ctor_data_args;
        self.stores().term().set(original_term_id, term.into());
        self.sub_ops().apply_sub_to_ty_in_place(annotation_ty, &final_sub);

        for (data_arg, result_data_arg) in term.data_args.iter().zip(subbed_ctor_result_args.iter())
        {
            let data_arg = self.get_arg(data_arg);
            let result_data_arg = self.get_arg(result_data_arg);
            if let Some(ty) = self.try_use_term_as_ty(data_arg.value) && let Ty::Hole(_) = self.get_ty(ty) {
                self.stores().term().set(data_arg.value, self.get_term(result_data_arg.value));
            }
        }

        Ok(())
    }

    /// Potentially run an expression at compile-time.
    ///
    /// This is only done if the expression has a `#run` annotation.
    pub fn potentially_run_expr(&self, expr: TermId, term_ty: TyId) -> TcResult<()> {
        if self.should_monomorphise() {
            let has_run_directive = self
                .stores()
                .directives()
                .get(expr.into())
                .map(|directives| directives.contains(IDENTS.run))
                == Some(true);
            if has_run_directive {
                let norm_ops = self.norm_ops();
                norm_ops.with_mode(NormalisationMode::Full { eval_impure_fns: true });
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
            norm_ops.with_mode(NormalisationMode::Full { eval_impure_fns: true });
            if norm_ops.normalise_in_place(fn_call.into())? {
                self.infer_term(fn_call, fn_call_result_ty)?;
            }
        }
        Ok(())
    }

    /// Infer the type of a function call.
    pub fn infer_fn_call_term(
        &self,
        fn_call_term: &FnCallTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        self.context().enter_scope(ScopeKind::Sub, || {
            self.normalise_and_check_ty(annotation_ty)?;
            let inferred_subject_ty = self.new_ty_hole_of(fn_call_term.subject);
            self.infer_term(fn_call_term.subject, inferred_subject_ty)?;

            match self.get_ty(inferred_subject_ty) {
                Ty::Fn(fn_ty) => {
                    // Potentially fill-in implicit args
                    if let Ty::Fn(_) = self.get_ty(fn_ty.return_ty) && fn_ty.implicit && !fn_call_term.implicit {
                        let applied_args = self.param_utils().instantiate_params_as_holes(fn_ty.params);
                        let copied_subject = self.new_term_from(fn_call_term.subject, self.get_term(fn_call_term.subject));
                        let new_subject = FnCallTerm {
                            args: applied_args,
                            subject: copied_subject,
                            implicit: fn_ty.implicit,
                        };
                        self.stores().term().set(fn_call_term.subject, new_subject.into());
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
                    let copied_return_ty = self.sub_ops().copy_ty(fn_ty.return_ty);

                    let mut fn_call_term = *fn_call_term;
                    self.infer_args(fn_call_term.args, copied_params, |inferred_fn_call_args| {
                        fn_call_term.args = inferred_fn_call_args;
                        self.stores().term().set(original_term_id, fn_call_term.into());

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

            self.infer_term(call_term, self.new_ty_hole())?;

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
        let fn_def = self.stores().fn_def().get(fn_def_id);
        let fn_ty = self.new_ty(fn_def.ty);
        self.infer_ty(annotation_ty, self.new_flexible_universe_ty())?;
        self.infer_ty(fn_ty, self.new_flexible_universe_ty())?;
        self.uni_ops().unify_tys(fn_ty, annotation_ty)?;

        let fn_ty_value = ty_as_variant!(self, self.get_ty(fn_ty), Fn);
        self.stores().fn_def().modify_fast(fn_def_id, |fn_def| fn_def.ty = fn_ty_value);

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
            let expected = self.new_expected_ty_of(original_term_id, self.new_ty(fn_ty));
            self.check_by_unify(expected, annotation_ty)?;
            return Ok(());
        }

        self.infer_fn_annotation_ty(fn_def_id, annotation_ty)?;
        let fn_def = self.get_fn_def(fn_def_id);

        if fn_mode == FnInferMode::Header {
            // If we are only inferring the header, then we also want to check for
            // immediate body functions.
            self.infer_params(fn_def.ty.params, || {
                self.infer_ty(fn_def.ty.return_ty, self.new_flexible_universe_ty())?;
                if let FnBody::Defined(fn_body) = fn_def.body {
                    if let Term::FnRef(immediate_body_fn) = self.get_term(fn_body) {
                        self.infer_fn_def(
                            immediate_body_fn,
                            self.new_ty_hole_of(fn_body),
                            fn_body,
                            FnInferMode::Header,
                        )?;
                    }
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

        let fn_def = self.get_fn_def(fn_def_id);

        match fn_def.body {
            FnBody::Defined(fn_body) => {
                self.context().enter_scope(ScopeKind::Fn(fn_def_id), || {
                    self.infer_params(fn_def.ty.params, || {
                        self.infer_ty(fn_def.ty.return_ty, self.new_flexible_universe_ty())?;
                        self.infer_term(fn_body, fn_def.ty.return_ty)
                    })
                })?;
            }
            FnBody::Intrinsic(_) | FnBody::Axiom => {}
        }

        let fn_ty_id = self.new_expected_ty_of(original_term_id, self.new_ty(fn_def.ty));
        self.check_by_unify(fn_ty_id, annotation_ty)?;

        self.register_atom_inference(fn_def_id, fn_def_id, fn_def.ty);
        Ok(())
    }

    /// Infer the type of a variable, and return it.
    pub fn infer_var(&self, term: Symbol, annotation_ty: TyId) -> TcResult<()> {
        match self.context().try_get_binding(term) {
            Some(binding) => match binding.kind {
                BindingKind::Decl(decl) => {
                    if let Some(ty) = decl.ty {
                        let ty = self.sub_ops().copy_ty(ty);
                        self.check_ty(ty)?;
                        self.uni_ops().unify_tys(ty, annotation_ty)?;
                        Ok(())
                    } else if decl.value.is_some() {
                        panic!("no type found for decl '{}'", self.env().with(decl))
                    } else {
                        panic!(
                            "Found declaration without type or value during inference: {}",
                            self.env().with(decl)
                        )
                    }
                }
                b => panic!("expected decl, but got {}", self.env().with(b)),
            },
            None => {
                panic!("no binding found for symbol '{}'", self.env().with(term))
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
        let closest_fn_def = self.context_utils().get_first_fn_def_in_scope();
        match closest_fn_def {
            Some(closest_fn_def) => {
                // Get the closest fn def in scope, and unify the
                // inferred expression type with its return type.
                // If successful, modify the fn def to set the return type to the inferred type.
                let closest_fn_def_return_ty =
                    self.stores().fn_def().map_fast(closest_fn_def, |def| def.ty.return_ty);
                self.infer_term(return_term.expression, closest_fn_def_return_ty)?;

                let inferred_ty = self.new_expected_ty_of(original_term, self.new_never_ty());
                self.check_by_unify(inferred_ty, annotation_ty)?;
                Ok(())
            }
            None => panic!("no fn def found in scope for return term"),
        }
    }

    /// Infer the type of a deref term, and return it.
    pub fn infer_deref_term(&self, deref_term: &DerefTerm, annotation_ty: TyId) -> TcResult<()> {
        let deref_inner_inferred = self.new_ty_hole_of(deref_term.subject);
        self.infer_term(deref_term.subject, deref_inner_inferred)?;

        let dereferenced_ty = match self.get_ty(deref_inner_inferred) {
            Ty::Ref(ref_ty) => ref_ty.ty,
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

    /// Infer the type of a type, and return it.
    pub fn infer_ty(&self, ty_id: TyId, annotation_ty: TyId) -> TcResult<()> {
        // @@Todo: properly deal with universes
        self.register_new_atom(ty_id, annotation_ty);
        let inner_is_ty =
            |ty: TyId| self.new_expected_ty_of_ty(ty, self.new_flexible_universe_ty());
        let expects_ty = |ty: TyId| self.check_by_unify(ty, inner_is_ty(ty));

        match self.get_ty(ty_id) {
            Ty::Eval(eval) => {
                self.infer_term(eval, annotation_ty)?;
            }
            Ty::Var(var) => self.infer_var(var, annotation_ty)?,
            Ty::Tuple(tuple_ty) => self.infer_params(tuple_ty.data, || Ok(()))?,
            Ty::Fn(fn_ty) => self.infer_params(fn_ty.params, || {
                self.infer_ty(fn_ty.return_ty, inner_is_ty(fn_ty.return_ty))
            })?,
            Ty::Ref(ref_ty) => {
                // Infer the inner type
                self.infer_ty(ref_ty.ty, inner_is_ty(ref_ty.ty))?;
            }
            Ty::Data(mut data_ty) => {
                let data_def = self.get_data_def(data_ty.data_def);
                let copied_params = self.sub_ops().copy_params(data_def.params);
                self.infer_args(data_ty.args, copied_params, |inferred_data_ty_args| {
                    data_ty.args = inferred_data_ty_args;
                    self.stores().ty().set(ty_id, data_ty.into());
                    Ok(())
                })?
            }
            Ty::Universe(_universe_ty) => {}
            Ty::Hole(_) => {}
        };

        // Ensure it is a type
        expects_ty(annotation_ty)?;

        self.register_atom_inference(ty_id, ty_id, annotation_ty);
        self.potentially_dump_tir(ty_id);

        Ok(())
    }

    /// Infer the type of a loop control term, and return it.
    pub fn infer_loop_control_term(
        &self,
        _: &LoopControlTerm,
        annotation_ty: TyId,
    ) -> TcResult<()> {
        // Always `never`.
        self.check_by_unify(self.new_never_ty(), annotation_ty)
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
        self.infer_block_term(&loop_term.block, self.new_ty_hole(), original_term_id)?;
        let loop_term = self.new_expected_ty_of(original_term_id, self.new_void_ty());
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
            let stack = self.stores().stack().get(block_term.stack_id);
            if let Some(local_mod_def) = stack.local_mod_def {
                // @@Improvement: it would be nice to pass through local
                // mod defs in two stages as well.
                self.infer_mod_def(local_mod_def, FnInferMode::Body)?;
            }

            // Keep track of statements diverging, so we can infer the appropriate return
            // type.
            let mut diverges = false;

            for statement in block_term.statements.iter() {
                let statement = self.stores().term_list().get_element(statement);

                let statement_ty = self.new_ty_hole_of(statement);
                self.infer_term(statement, statement_ty)?;

                // If the statement diverges, we can already exit
                if self.uni_ops().is_uninhabitable(statement_ty)? {
                    diverges = true;
                }
            }

            if diverges {
                match self.get_ty(annotation_ty) {
                    Ty::Hole(_) => {
                        // If it diverges, we can just infer the return type as `never`.
                        let block_term_ty =
                            self.new_expected_ty_of(original_term_id, self.new_never_ty());
                        self.check_by_unify(block_term_ty, annotation_ty)?;
                    }
                    _ => {
                        // Infer the return value
                        let return_value_ty = self.new_ty_hole_of(block_term.return_value);
                        self.infer_term(block_term.return_value, return_value_ty)?;
                    }
                }
            } else {
                // Infer the return value
                self.infer_term(block_term.return_value, annotation_ty)?;
            };

            let sub = self.sub_ops().create_sub_from_current_scope();
            self.sub_ops().apply_sub_to_ty_in_place(annotation_ty, &sub);

            let sub_ops = self.sub_ops();
            let vars_in_scope = sub_ops.get_unassigned_vars_in_current_scope();
            if sub_ops.atom_contains_vars(annotation_ty.into(), &vars_in_scope) {
                return Err(TcError::TryingToReferenceLocalsInType { ty: annotation_ty });
            }

            Ok(())
        })
    }

    /// Infer a `typeof` term, and return it.
    pub fn infer_type_of_term(
        &self,
        type_of_term: TypeOfTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        let inferred_ty = self.new_ty_hole_of(type_of_term.term);
        self.infer_term(type_of_term.term, inferred_ty)?;
        self.infer_ty(inferred_ty, annotation_ty)?;
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
        let annotation_ref_ty = match self.get_ty(annotation_ty) {
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

        self.infer_term(ref_term.subject, annotation_ref_ty.ty)?;

        let ty = self.new_expected_ty_of(original_term_id, self.new_ty(annotation_ref_ty));
        self.check_by_unify(ty, annotation_ty)?;
        Ok(())
    }

    /// Infer a cast term, and return its type.
    pub fn infer_cast_term(&self, cast_term: CastTerm, annotation_ty: TyId) -> TcResult<()> {
        self.infer_term(cast_term.subject_term, cast_term.target_ty)?;
        self.check_by_unify(cast_term.target_ty, annotation_ty)?;
        Ok(())
    }

    /// Infer a stack declaration term, and return its type.
    pub fn infer_decl_term(&self, decl_term: &DeclTerm, annotation_ty: TyId) -> TcResult<()> {
        self.check_ty(decl_term.ty)?;
        if let Some(value) = decl_term.value {
            self.infer_term(value, decl_term.ty)?;
        };
        self.infer_pat(decl_term.bind_pat, decl_term.ty, decl_term.value)?;
        self.check_by_unify(self.new_void_ty(), annotation_ty)?;
        Ok(())
    }

    /// Infer an access term.
    pub fn infer_access_term(
        &self,
        access_term: &AccessTerm,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<()> {
        let subject_ty = self.new_ty_hole_of(access_term.subject);
        self.infer_term(access_term.subject, subject_ty)?;

        let params = match self.get_ty(subject_ty) {
            Ty::Tuple(tuple_ty) => tuple_ty.data,
            Ty::Data(data_ty) => {
                match self.data_utils().get_single_ctor_of_data_def(data_ty.data_def) {
                    Some(ctor) => {
                        let data_def = self.get_data_def(data_ty.data_def);
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

        if let Some(param) = self.try_get_param_by_index(params, access_term.field) {
            // Create a substitution that maps the parameters of the record
            // type to the corresponding fields of the record term.
            //
            // i.e. `x: (T: Type, t: T);  x.t: x.T`
            let param_access_sub =
                self.sub_ops().create_sub_from_param_access(params, access_term.subject);
            let subbed_param_ty = self.sub_ops().apply_sub_to_ty(param.ty, &param_access_sub);
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

        let subject_ty = self.new_ty_hole_of(index_term.subject);
        self.infer_term(index_term.subject, subject_ty)?;
        self.normalise_and_check_ty(subject_ty)?;

        // Ensure the index is a usize
        let index_ty =
            self.new_expected_ty_of(index_term.index, self.new_data_ty(self.primitives().usize()));
        self.infer_term(index_term.index, index_ty)?;

        let wrong_subject_ty = || {
            Err(TcError::WrongTy {
                term: original_term_id,
                inferred_term_ty: subject_ty,
                kind: WrongTermKind::NotAnArray,
            })
        };

        // Ensure that the subject is array-like
        let inferred_ty = match self.get_ty(subject_ty) {
            Ty::Data(data_ty) => {
                let data_def = self.get_data_def(data_ty.data_def);
                if let DataDefCtors::Primitive(PrimitiveCtorInfo::Array(array_primitive)) =
                    data_def.ctors
                {
                    let sub = self
                        .sub_ops()
                        .create_sub_from_args_of_params(data_ty.args, data_def.params);
                    let array_ty = self.sub_ops().apply_sub_to_ty(array_primitive.element_ty, &sub);
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
        let subject_ty = self.new_ty_hole_of(assign_term.subject);
        self.infer_term(assign_term.subject, subject_ty)?;

        let value_ty = self.new_ty_hole_of(assign_term.value);
        self.infer_term(assign_term.value, value_ty)?;

        self.check_by_unify(value_ty, subject_ty)?;

        let inferred_ty = self.new_expected_ty_of(original_term_id, self.new_void_ty());
        self.check_by_unify(inferred_ty, annotation_ty)?;
        Ok(())
    }

    /// Infer a match term.
    pub fn infer_match_term(&self, match_term: &MatchTerm, annotation_ty: TyId) -> TcResult<()> {
        self.check_ty(annotation_ty)?;
        let match_subject_ty = self.new_ty_hole_of(match_term.subject);
        self.infer_term(match_term.subject, match_subject_ty)?;

        let match_subject_var = match self.get_term(match_term.subject) {
            Term::Var(v) => Some(v),
            _ => None,
        };

        let match_annotation_ty = match self.get_ty(annotation_ty) {
            Ty::Hole(_) => None,
            t => Some(t),
        };

        let mut unified_ty = annotation_ty;
        let inhabited = Cell::new(false);
        for case in match_term.cases.iter() {
            let case_data = self.stores().match_cases().get_element(case);
            self.context().enter_scope(case_data.stack_id.into(), || -> TcResult<_> {
                let subject_ty_copy = self.sub_ops().copy_ty(match_subject_ty);

                self.infer_pat(case_data.bind_pat, subject_ty_copy, Some(match_term.subject))?;
                let new_unified_ty =
                    self.new_expected_ty_of(case_data.value, self.sub_ops().copy_ty(unified_ty));

                if let Some(match_subject_var) = match_subject_var {
                    if let Some(pat_term) = self.try_use_pat_as_term(case_data.bind_pat) {
                        self.context_utils().add_assignment(
                            match_subject_var,
                            subject_ty_copy,
                            pat_term,
                        );
                    }
                }

                match match_annotation_ty {
                    _ if self.uni_ops().is_uninhabitable(subject_ty_copy)? => {
                        let new_unified_ty = self.new_ty_hole_of(case_data.value);
                        self.infer_term(case_data.value, new_unified_ty)?;
                        self.check_by_unify(new_unified_ty, self.new_never_ty())?;
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
                            self.uni_ops().unify_tys(new_unified_ty, unified_ty)?;
                            unified_ty = new_unified_ty;
                        }
                    }
                }

                Ok(())
            })?
        }

        if matches!(self.get_ty(unified_ty), Ty::Hole(_)) {
            if !inhabited.get() {
                unified_ty = self.new_expected_ty_of_ty(unified_ty, self.new_never_ty());
            } else {
                unified_ty = self.new_expected_ty_of_ty(unified_ty, self.new_void_ty());
            }
        }

        self.check_by_unify(unified_ty, annotation_ty)?;
        Ok(())
    }

    /// Infer a concrete type for a given term.
    ///
    /// If this is not possible, return `None`.
    /// To create a hole when this is not possible, use
    /// [`InferOps::infer_ty_of_term_or_hole`].
    pub fn infer_term(&self, term_id: TermId, annotation_ty: TyId) -> TcResult<()> {
        self.register_new_atom(term_id, annotation_ty);

        match self.get_term(term_id) {
            Term::Tuple(tuple_term) => {
                self.infer_tuple_term(&tuple_term, annotation_ty, term_id)?
            }
            Term::Lit(lit_term) => self.infer_lit(&lit_term, annotation_ty)?,
            Term::Array(prim_term) => self.infer_array_term(&prim_term, annotation_ty, term_id)?,
            Term::Ctor(ctor_term) => self.infer_ctor_term(&ctor_term, annotation_ty, term_id)?,
            Term::FnCall(fn_call_term) => {
                self.infer_fn_call_term(&fn_call_term, annotation_ty, term_id)?
            }
            Term::FnRef(fn_def_id) => {
                self.infer_fn_def(fn_def_id, annotation_ty, term_id, FnInferMode::Body)?
            }
            Term::Var(var_term) => self.infer_var(var_term, annotation_ty)?,
            Term::Return(return_term) => {
                self.infer_return_term(&return_term, annotation_ty, term_id)?
            }
            Term::Ty(ty_id) => self.infer_ty(ty_id, annotation_ty)?,
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
                self.infer_type_of_term(ty_of_term, annotation_ty, term_id)?
            }
            Term::Ref(ref_term) => self.infer_ref_term(&ref_term, annotation_ty, term_id)?,
            Term::Cast(cast_term) => self.infer_cast_term(cast_term, annotation_ty)?,
            Term::Decl(decl_term) => self.infer_decl_term(&decl_term, annotation_ty)?,
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
            Term::Hole(_) => {}
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
        self.infer_lit(&range_pat.start.into(), annotation_ty)?;
        self.infer_lit(&range_pat.end.into(), annotation_ty)?;
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
        let params = match self.get_ty(annotation_ty) {
            Ty::Tuple(tuple_ty) => tuple_ty.data,
            Ty::Hole(_) => self.param_utils().create_hole_params_from_args(tuple_pat.data),
            _ => {
                let inferred = self.param_utils().create_hole_params_from_args(tuple_pat.data);
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: self.new_expected_ty_of(
                        original_pat_id,
                        self.new_ty(TupleTy { data: inferred }),
                    ),
                    inferred_from: Some(original_pat_id.into()),
                });
            }
        };
        let mut tuple_pat = *tuple_pat;
        self.infer_pat_args(tuple_pat.data, tuple_pat.data_spread, params, |new_args| {
            tuple_pat.data = new_args;
            self.stores().pat().set(original_pat_id, tuple_pat.into());
            Ok(())
        })?;

        let tuple_ty =
            self.new_expected_ty_of(original_pat_id, self.new_ty(TupleTy { data: params }));
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
        let list_annotation_inner_ty = match self.get_ty(annotation_ty) {
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

        self.infer_unified_pat_list(list_pat.pats, list_annotation_inner_ty)?;
        let list_ty = DataTy {
            data_def: self.primitives().list(),
            args: self.new_args(&[self.new_term(list_annotation_inner_ty)]),
        };
        self.check_by_unify(self.new_ty(list_ty), annotation_ty)?;
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
        let ctor = self.get_ctor_def(ctor_def_id);
        let data_def = self.get_data_def(ctor.data_def_id);

        // Ensure the annotation is valid
        self.normalise_and_check_ty(annotation_ty)?;

        // Get the annotation as a DataTy, or create a hole one if not given
        let mut annotation_data_ty = match self.get_ty(annotation_ty) {
            Ty::Data(data) if data.data_def == ctor.data_def_id => DataTy {
                data_def: data_def.id,
                args: if data.args.len() == 0 {
                    self.param_utils().instantiate_params_as_holes(data_def.params)
                } else {
                    data.args
                },
            },
            Ty::Hole(_) => DataTy {
                data_def: data_def.id,
                args: self.param_utils().instantiate_params_as_holes(data_def.params),
            },
            _ => {
                return Err(TcError::MismatchingTypes {
                    expected: annotation_ty,
                    actual: self.new_ty(DataTy { args: data_args, data_def: ctor.data_def_id }),
                    inferred_from: Some(original_atom.into()),
                });
            }
        };

        // Get the data arguments given to the constructor, like Equal<...>::Refl(...)
        //                                                             ^^^ these
        let ctor_data_args = if data_args.len() == 0 {
            self.param_utils().instantiate_params_as_holes(data_def.params)
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
                self.sub_ops().apply_sub_to_pat_args_in_place(inferred_pat_ctor_args, &ctor_sub);
                self.sub_ops().apply_sub_to_args_in_place(inferred_ctor_data_args, &ctor_sub);

                // These arguments might have been updated so we need to set them
                pat.data_args = inferred_ctor_data_args;
                pat.ctor_pat_args = inferred_pat_ctor_args;
                self.stores().pat().set(original_pat_id, pat.into());

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
            self.new_expected_ty_of(original_atom, self.new_ty(annotation_data_ty));
        let uni_ops = self.uni_ops();
        uni_ops.with_binds(binds);
        uni_ops.add_unification_from_sub(&resulting_sub);
        uni_ops.unify_tys(expected_data_ty, annotation_ty)?;

        // Now we gather the final substitution, and apply it to the result
        // arguments, the constructor data arguments, and finally the annotation
        // type.
        let final_sub = self.sub_ops().create_sub_from_current_scope();
        self.sub_ops().apply_sub_to_args_in_place(subbed_ctor_result_args, &final_sub);
        self.sub_ops().apply_sub_to_args_in_place(inferred_ctor_data_args, &final_sub);
        // Set data args because they might have been updated again
        pat.data_args = inferred_ctor_data_args;
        self.stores().pat().set(original_pat_id, pat.into());
        self.sub_ops().apply_sub_to_ty_in_place(annotation_ty, &final_sub);

        for (data_arg, result_data_arg) in pat.data_args.iter().zip(subbed_ctor_result_args.iter())
        {
            let data_arg = self.get_arg(data_arg);
            let result_data_arg = self.get_arg(result_data_arg);
            if let Some(ty) = self.try_use_term_as_ty(data_arg.value)
                && let Ty::Hole(_) = self.get_ty(ty)
            {
                self.stores().term().set(data_arg.value, self.get_term(result_data_arg.value));
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
        let expected_condition_ty =
            self.new_expected_ty_of(pat.condition, self.new_data_ty(self.primitives().bool()));
        self.infer_term(pat.condition, expected_condition_ty)?;
        if let Term::Var(v) = self.get_term(pat.condition) {
            self.context_utils().add_assignment(v, expected_condition_ty, self.new_bool_term(true));
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

        match self.get_pat(pat_id) {
            Pat::Binding(var) => {
                self.check_ty(annotation_ty)?;
                match binds_to {
                    Some(value)
                        if self.norm_ops().atom_has_effects(value.into()) == Some(false) =>
                    {
                        self.context_utils().add_assignment_to_closest_stack(
                            var.name,
                            annotation_ty,
                            value,
                        );
                    }
                    _ => {
                        self.context_utils().add_typing_to_closest_stack(var.name, annotation_ty);
                    }
                }
            }
            Pat::Range(range_pat) => self.infer_range_pat(range_pat, annotation_ty)?,
            Pat::Lit(lit) => self.infer_lit(&lit.into(), annotation_ty)?,
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
        let (ctor_data_def_id, ctor_params, ctor_result_args) =
            self.stores().ctor_defs().map_fast(ctor.0, |ctors| {
                (ctors[ctor.1].data_def_id, ctors[ctor.1].params, ctors[ctor.1].result_args)
            });
        self.infer_params(ctor_params, || {
            let return_ty =
                self.new_ty(DataTy { data_def: ctor_data_def_id, args: ctor_result_args });
            self.infer_ty(return_ty, self.new_ty_hole())?;
            Ok(())
        })
    }

    /// Infer the given data definition.
    pub fn infer_data_def(&self, data_def_id: DataDefId) -> TcResult<()> {
        let (data_def_params, data_def_ctors) = self
            .stores()
            .data_def()
            .map_fast(data_def_id, |data_def| (data_def.params, data_def.ctors));

        self.infer_params(data_def_params, || {
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
                            self.infer_ty(array_ctor_info.element_ty, self.new_ty_hole())?;
                            if let Some(length) = array_ctor_info.length {
                                self.infer_term(
                                    length,
                                    self.new_data_ty(self.primitives().usize()),
                                )?;
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
