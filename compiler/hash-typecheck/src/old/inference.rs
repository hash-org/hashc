//! Operations to infer types of terms and patterns.

use std::{collections::HashSet, ops::ControlFlow};

use hash_attrs::{attr::attr_store, builtin::attrs};
use hash_exhaustiveness::ExhaustivenessChecker;
use hash_reporting::diagnostic::Diagnostics;
use hash_source::{entry_point::EntryPointKind, identifier::IDENTS, ModuleKind};
use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    TrivialSequenceStoreKey,
};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::{HasContext, ScopeKind},
    dump::dump_tir,
    intrinsics::{
        definitions::list_ty,
        utils::{try_use_ty_as_float_ty, try_use_ty_as_int_ty},
    },
    term_as_variant,
    tir::{
        validate_and_reorder_pat_args_against_params, validate_params, Arg, ArgsId, CallTerm,
        DataDefCtors, FnDefId, FnTy, HasAstNodeId, Lit, LitId, Node, NodeId, NodeOrigin, NodesId,
        ParamsId, Pat, PatArgsId, PatId, PatListId, PatOrCapture, PrimitiveCtorInfo, Spread,
        SymbolId, Term, TermId, TermListId, Ty, TyId,
    },
    visitor::{Atom, Map, Visit, Visitor},
};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::{TcError, TcResult},
    operations::{normalisation::NormalisationMode, OperationsOnNode, RecursiveOperationsOnNode},
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
            self.check_node(term, ty)
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
                self.check_node(pat, (ty, None))?;
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
                        self.check_node(pat, (param_ty, None))?;
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
                    self.check_node(param.ty, Ty::universe_of(param.ty))?;
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
            _ => self.check_node(ty, Ty::universe_of(ty)),
        }
    }

    /// Check that the given type is well-formed, and normalise it.
    pub fn normalise_and_check_ty(&self, ty: TyId) -> TcResult<()> {
        match *ty.value() {
            Ty::Hole(_) => Ok(()),
            _ => {
                self.check_node(ty, Ty::universe_of(ty))?;
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
                    self.check_node(expr, term_ty)?;
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
                self.check_node(fn_call, fn_call_result_ty)?;
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

            self.check_node(call_term, Ty::hole_for(call_term))?;

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
        self.check_node(annotation_ty, Ty::universe_of(annotation_ty))?;
        self.check_node(fn_ty, Ty::universe_of(fn_ty))?;
        self.uni_ops().unify_terms(fn_ty, annotation_ty)?;

        let fn_ty_value = term_as_variant!(self, fn_ty.value(), FnTy);
        fn_def_id.borrow_mut().ty = fn_ty_value;

        Ok(fn_ty_value)
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
}
