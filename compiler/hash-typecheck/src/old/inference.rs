//! Operations to infer types of terms and patterns.

use std::{collections::HashSet, ops::ControlFlow};

use hash_attrs::{attr::attr_store, builtin::attrs};
use hash_exhaustiveness::ExhaustivenessChecker;
use hash_reporting::diagnostic::{Diagnostics, ErrorState};
use hash_source::{entry_point::EntryPointKind, identifier::IDENTS, ModuleKind};
use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::{HasContext, ScopeKind},
    dump::dump_tir,
    intrinsics::{
        definitions::{array_ty, bool_ty, list_def, list_ty, usize_ty, Intrinsic},
        make::IsIntrinsic,
        utils::{
            bool_term, create_term_from_usize_lit, try_use_ty_as_float_ty, try_use_ty_as_int_ty,
        },
    },
    term_as_variant,
    tir::{
        validate_and_reorder_pat_args_against_params, validate_params, Arg, ArgId, ArgsId,
        ArrayPat, ArrayTerm, CallTerm, CtorDefId, CtorPat, DataDefCtors, DataDefId, DataTy,
        FnDefId, FnTy, HasAstNodeId, IfPat, Lit, LitId, ModDefId, ModMemberId, ModMemberValue,
        Node, NodeId, NodeOrigin, NodesId, OrPat, Param, ParamsId, Pat, PatArgsId, PatId,
        PatListId, PatOrCapture, PrimitiveCtorInfo, RangePat, Spread, SymbolId, Term, TermId,
        TermListId, TuplePat, TupleTy, Ty, TyId,
    },
    visitor::{Atom, Map, Visit, Visitor},
};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::{TcError, TcResult},
    operations::{
        normalisation::NormalisationMode, Operations, OperationsOnNode, RecursiveOperationsOnNode,
    },
};

/// The mode in which to infer the type of a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnInferMode {
    /// Infer the type of a function but do not look at its body.
    Header,
    /// Infer the type of a function and its body.
    Body,
}

impl<T: TcEnv> Tc<'_, T> {
    /// Create a new [ExhaustivenessChecker] so it can be used to check
    /// refutability or exhaustiveness of patterns.
    pub fn exhaustiveness_checker<U: HasAstNodeId>(&self, subject: U) -> ExhaustivenessChecker<T> {
        let location = subject.span().unwrap();
        ExhaustivenessChecker::new(location, self.env)
    }

    /// Merge all of the produced diagnostics into the current diagnostics.
    ///
    /// @@Hack: remove this when we have a better way to send exhaustiveness
    /// jobs and add them to general tc diagnostics.
    pub fn append_exhaustiveness_diagnostics(&self, checker: ExhaustivenessChecker<T>) {
        let (errors, warnings) = checker.into_diagnostics().into_diagnostics();

        for error in errors {
            self.diagnostics().add_error(error.into())
        }

        for warning in warnings {
            self.diagnostics().add_warning(warning.into())
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
                    let param_ty = Visitor::new().copy(param.ty);
                    infer_arg(&arg, param_ty)?;
                    self.sub_ops().apply_sub_from_context(param_ty);
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
            self.infer_term(term, ty)
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
        in_arg_scope: impl FnMut(ArgsId) -> TcResult<U>,
    ) -> TcResult<U> {
        self.check_node_rec(args, annotation_params, in_arg_scope)
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
                    PatOrCapture::Pat(pat) => pat.try_use_as_term(),
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
            Ty::Universe(_) | Ty::Hole(_) => Ok(()),
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

    /// Potentially adjust the underlying constant of a literal after its type
    /// has been inferred.
    ///
    /// This might be needed if a literal is unsuffixed in the original source,
    /// and thus represented as something other than its true type in the
    /// `CONSTS`. After `infer_lit`, its true type will be known, and
    /// we can then adjust the underlying constant to match the true type.
    pub fn bake_lit_repr(&self, lit: LitId, inferred_ty: TyId) -> TcResult<()> {
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
                        Lit::Int(fl) => fl.bake(self.target(), int_ty),
                        _ => unreachable!(),
                    })?;
                }
                // @@Incomplete: as above
            }
            _ => {}
        }
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
                            let copied_params = Visitor::new().copy(data_def.params);
                            self.infer_args(data.args, copied_params, |_| {
                                let sub = self.sub_ops().create_sub_from_current_scope();
                                let subbed_element_ty =
                                    self.sub_ops().apply_sub(array_prim.element_ty, &sub);
                                let subbed_index =
                                    array_prim.length.map(|l| self.sub_ops().apply_sub(l, &sub));
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

        let array_len_origin = array_term.length_origin();
        let (inner_ty, array_len) = self
            .use_ty_as_array(annotation_ty)?
            .unwrap_or_else(|| (Ty::hole(array_len_origin.inferred()), None));

        // Now unify that the terms that are specified in the array match the
        // annotation type.
        let inferred_len_term = match *array_term {
            ArrayTerm::Normal(elements) => {
                self.infer_unified_term_list(elements, inner_ty)?;
                create_term_from_usize_lit(self.target(), elements.len(), array_len_origin)
            }
            ArrayTerm::Repeated(term, repeat) => {
                self.infer_term(term, inner_ty)?;
                self.infer_term(repeat, usize_ty(array_len_origin))?;
                repeat
            }
        };

        // Ensure the array lengths match if given
        if let Some(len) = array_len {
            if !self.uni_ops().terms_are_equal(len, inferred_len_term) {
                return Err(TcError::MismatchingArrayLengths {
                    expected_len: len,
                    got_len: inferred_len_term,
                });
            }
        }

        // Either create  a default type, or apply a substitution to the annotation
        // type.
        //
        // - If the array kind is "repeated", the default annotation that we use is an
        //   array of the specified length.
        //
        // - Otherwise, we just default to a list type.
        if let Ty::Hole(_) = *annotation_ty.value() {
            let default_annotation = match array_term {
                ArrayTerm::Normal(_) => list_ty(inner_ty, NodeOrigin::Expected),
                ArrayTerm::Repeated(_, repeat) => array_ty(inner_ty, *repeat, NodeOrigin::Expected),
            };

            self.check_by_unify(default_annotation, annotation_ty)?
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
        Visitor::new().visit(pat, &mut |atom| self.get_binds_in_pat_atom_once(atom, &mut binds));
        binds
    }

    pub fn get_binds_in_pat_args(&self, pat_args: PatArgsId) -> HashSet<SymbolId> {
        let mut binds = HashSet::new();
        Visitor::new()
            .visit(pat_args, &mut |atom| self.get_binds_in_pat_atom_once(atom, &mut binds));
        binds
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

        let kind = self.current_source().module_kind();

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

    /// Infer an intrinsic term, and return it.
    pub fn infer_intrinsic(&self, intrinsic: Intrinsic, annotation_ty: TyId) -> TcResult<()> {
        // ##GeneratedOrigin: intrinsics do not belong to the source code
        self.check_by_unify(Term::from(intrinsic.ty(), NodeOrigin::Generated), annotation_ty)?;
        Ok(())
    }

    /// Infer a concrete type for a given term.
    pub fn infer_term(&self, term_id: TermId, annotation_ty: TyId) -> TcResult<()> {
        self.register_new_atom(term_id, annotation_ty);
        match *term_id.value() {
            Term::Tuple(mut tuple_term) => self.check(&mut tuple_term, annotation_ty, term_id)?,
            Term::Lit(lit_term) => self.check_node(lit_term, annotation_ty)?,
            Term::Array(mut prim_term) => { self.check(&mut prim_term, annotation_ty, term_id) }?,
            Term::Ctor(mut ctor_term) => self.check(&mut ctor_term, annotation_ty, term_id)?,
            Term::Call(mut call_term) => self.check(&mut call_term, annotation_ty, term_id)?,
            Term::Fn(fn_def_id) => {
                self.check(&mut (fn_def_id, FnInferMode::Body), annotation_ty, term_id)?
            }
            Term::Var(mut var_term) => self.check(&mut var_term, annotation_ty, term_id)?,
            Term::Return(mut return_term) => {
                self.check(&mut return_term, annotation_ty, term_id)?
            }
            Term::Deref(mut deref_term) => self.check(&mut deref_term, annotation_ty, term_id)?,
            Term::LoopControl(mut loop_control_term) => {
                self.check(&mut loop_control_term, annotation_ty, term_id)?
            }
            Term::Unsafe(mut unsafe_term) => {
                self.check(&mut unsafe_term, annotation_ty, term_id)?
            }
            Term::Loop(mut loop_term) => self.check(&mut loop_term, annotation_ty, term_id)?,
            Term::Block(mut block_term) => self.check(&mut block_term, annotation_ty, term_id)?,
            Term::TyOf(mut ty_of_term) => self.check(&mut ty_of_term, annotation_ty, term_id)?,
            Term::Ref(mut ref_term) => self.check(&mut ref_term, annotation_ty, term_id)?,
            Term::Cast(mut cast_term) => self.check(&mut cast_term, annotation_ty, term_id)?,
            Term::Access(mut access_term) => {
                self.check(&mut access_term, annotation_ty, term_id)?
            }
            Term::Index(mut index_term) => self.check(&mut index_term, annotation_ty, term_id)?,
            Term::Match(mut match_term) => self.check(&mut match_term, annotation_ty, term_id)?,
            Term::Assign(mut assign_term) => {
                self.check(&mut assign_term, annotation_ty, term_id)?
            }
            Term::Intrinsic(mut intrinsic) => self.check(&mut intrinsic, annotation_ty, term_id)?,
            Term::Hole(mut hole) => self.check(&mut hole, annotation_ty, term_id)?,
            Ty::TupleTy(mut tuple_ty) => self.check(&mut tuple_ty, annotation_ty, term_id)?,
            Ty::FnTy(mut fn_ty) => self.check(&mut fn_ty, annotation_ty, term_id)?,
            Ty::RefTy(mut ref_ty) => {
                self.check(&mut ref_ty, annotation_ty, term_id)?;
            }
            Ty::DataTy(mut data_ty) => {
                self.check(&mut data_ty, annotation_ty, term_id)?;
            }
            Ty::Universe(mut universe_ty) => {
                self.check(&mut universe_ty, annotation_ty, term_id)?
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

        lo.map(|lo| self.check_node(*lo, annotation_ty)).transpose()?;
        hi.map(|hi| self.check_node(*hi, annotation_ty)).transpose()?;

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
        let copied_params = Visitor::new().copy(data_def.params);
        let (inferred_ctor_data_args, subbed_ctor_params, subbed_ctor_result_args) = self
            .infer_args(ctor_data_args, copied_params, |inferred_data_args| {
                let sub = self.sub_ops().create_sub_from_current_scope();
                let subbed_ctor_params = self.sub_ops().apply_sub(ctor.params, &sub);
                let subbed_ctor_result_args = self.sub_ops().apply_sub(ctor.result_args, &sub);
                self.sub_ops().apply_sub_in_place(inferred_data_args, &sub);
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
                self.sub_ops().apply_sub_in_place(subbed_ctor_result_args, &ctor_sub);
                self.sub_ops().apply_sub_in_place(inferred_pat_ctor_args, &ctor_sub);
                self.sub_ops().apply_sub_in_place(inferred_ctor_data_args, &ctor_sub);

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
        self.sub_ops().apply_sub_in_place(subbed_ctor_result_args, &final_sub);
        self.sub_ops().apply_sub_in_place(inferred_ctor_data_args, &final_sub);
        self.sub_ops().apply_sub_in_place(pat.ctor_pat_args, &final_sub);
        // Set data args because they might have been updated again
        pat.data_args = inferred_ctor_data_args;
        original_pat_id.set(original_pat_id.value().with_data(pat.into()));
        self.sub_ops().apply_sub_in_place(annotation_ty, &final_sub);

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
                v.symbol,
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
            Pat::Lit(lit) => self.check_node(*lit, annotation_ty)?,
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
                self.check(
                    &mut (fn_def_id, fn_mode),
                    Ty::hole(fn_def_id.origin().inferred()),
                    Term::hole(fn_def_id.origin()),
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
