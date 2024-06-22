use std::ops::ControlFlow;

use hash_storage::store::statics::StoreId;
use hash_storage::store::sequence::SequenceStoreKey;
use hash_tir::{
    context::HasContext, intrinsics::make::IsIntrinsic, tir::{ArgsId, CallTerm, NodeId, NodesId, Term, TermId, TyId}
};
use itertools::Itertools;

use crate::{
    diagnostics::{TcError, TcResult, WrongTermKind},
    env::TcEnv,
    options::normalisation::{
        normalised_if, normalised_option, normalised_to, NormalisationMode, NormalisationState,
        NormaliseResult, NormaliseSignal,
    },
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode},
    utils::intrinsic_abilities::IntrinsicAbilitiesImpl,
};

impl<E: TcEnv> Tc<'_, E> {
    /// Check some args against the given subject function type.
    pub(crate) fn check_args_against_fn_ty(
        &self,
        subject_ty_id: TyId,
        args: ArgsId,
        args_implicit: bool,
        annotation_ty: TyId,
        original_term_id: TermId,
    ) -> TcResult<Option<ArgsId>> {
        let (fn_ty, insert_implicit) = self.try_or_normalise(subject_ty_id, |subject, _| {
            let subject_ty = subject.value();
            match subject_ty.data {
                Term::FnTy(fn_ty) if fn_ty.implicit == args_implicit => Ok((fn_ty, false)),
                Term::FnTy(fn_ty) if fn_ty.implicit && !args_implicit => Ok((fn_ty, true)),
                _ => Err(TcError::WrongTerm {
                    kind: WrongTermKind::NotAFunction,
                    inferred_term_ty: subject,
                    term: original_term_id,
                }),
            }
        })?;

        if insert_implicit {
            // Implicit argument insertion
            let implicit_args = self.args_from_params_as_holes(fn_ty.params);
            Ok(Some(implicit_args))
        } else {
            // Check arguments
            self.check_node(args, fn_ty.params)?;
            let s = self.substituter();
            let sub = s.create_sub_from_args_of_params(args, fn_ty.params);
            let subbed_return_ty = s.apply_sub(fn_ty.return_ty, &sub);
            self.unify_nodes(subbed_return_ty, annotation_ty)?;
            Ok(None)
        }
    }
}

impl<E: TcEnv> OperationsOn<CallTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        call_term: &mut CallTerm,
        annotation_ty: Self::AnnotNode,
        original_term_id: Self::Node,
    ) -> TcResult<()> {
        let inferred_subject_ty = self.fresh_meta_for(call_term.subject);
        self.check_node(call_term.subject, inferred_subject_ty)?;
        match self.check_args_against_fn_ty(inferred_subject_ty, call_term.args, call_term.implicit, annotation_ty, original_term_id)? {
            Some(inserted_args) => {
                let copied_subject =
                    Term::inherited_from(call_term.subject, *call_term.subject.value());
                let new_subject = CallTerm { args: inserted_args, subject: copied_subject, implicit: true };
                call_term.subject.set(call_term.subject.value().with_data(new_subject.into()));
                self.check(call_term, annotation_ty, original_term_id)
            }
            None => Ok(())
        }
    }

    fn try_normalise(
        &self,
        mut fn_call: CallTerm,
        item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<TermId>> {
        let st = NormalisationState::new();

        fn_call.subject = self.normalise_node_and_record(fn_call.subject, &st)?;
        fn_call.args =
            st.update_from_result(fn_call.args, self.potentially_normalise_node(fn_call.args))?;

        let subject = *fn_call.subject.value();

        // Beta-reduce:
        if let Term::Fn(fn_def_id) = subject {
            let fn_def = fn_def_id.value();
            if fn_def.ty.pure
                || matches!(self.normalisation_opts.mode.get(), NormalisationMode::Full)
            {
                return self.context().enter_scope(fn_def_id.into(), || {
                    // Add argument bindings:
                    self.context().add_arg_bindings(fn_def.ty.params, fn_call.args);

                    // Evaluate result:
                    match self.normalise_node(fn_def.body) {
                        Err(NormaliseSignal::Return(result)) | Ok(result) => {
                            // Substitute remaining bindings:
                            let sub = self.substituter().create_sub_from_current_scope();
                            let result = self.substituter().apply_sub(result, &sub);
                            normalised_to(result)
                        }
                        Err(e) => Err(e),
                    }
                });
            }
        } else if let Term::Intrinsic(intrinsic) = subject {
            return self.context().enter_scope(intrinsic.into(), || {
                let args_as_terms =
                    fn_call.args.elements().borrow().iter().map(|arg| arg.value).collect_vec();

                // Run intrinsic:
                let result: Option<TermId> = intrinsic
                    .call(IntrinsicAbilitiesImpl::new(self), &args_as_terms)
                    .map_err(TcError::Intrinsic)?;

                normalised_option(result)
            });
        }

        normalised_if(|| Term::from(fn_call, item_node.origin().computed()), &st)
    }

    fn unify(
        &self,
        src: &mut CallTerm,
        target: &mut CallTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        self.unify_nodes(src.subject, target.subject)?;
        self.unify_nodes(src.args, target.args)?;
        Ok(())
    }
}
