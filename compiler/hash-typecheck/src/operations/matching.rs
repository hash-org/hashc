use std::{cell::Cell, ops::ControlFlow};

use hash_storage::store::{statics::StoreId, SequenceStoreKey, TrivialSequenceStoreKey};
use hash_tir::{
    context::HasContext,
    intrinsics::definitions::never_ty,
    tir::{MatchTerm, NodeOrigin, NodesId, Term, TermId, Ty, TyId},
    visitor::Map,
};
use itertools::Itertools;

use crate::{
    diagnostics::TcResult,
    env::TcEnv,
    options::normalisation::{
        normalised_to, stuck_normalising, NormalisationState, NormaliseResult, NormaliseSignal,
    },
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode},
    utils::matching::MatchResult,
};

impl<E: TcEnv> OperationsOn<MatchTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        match_term: &mut MatchTerm,
        annotation_ty: Self::AnnotNode,
        _original_node_id: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        let match_subject_ty = self.fresh_meta_for(match_term.subject);
        self.check_node(match_term.subject, match_subject_ty)?;

        let match_subject_var = match *match_term.subject.value() {
            Term::Var(v) => Some(v),
            _ => None,
        };

        let match_annotation_ty = match *annotation_ty.value() {
            Ty::Meta(_) => None,
            t => Some(t),
        };

        let mut unified_ty = annotation_ty;
        let inhabited = Cell::new(false);
        for case in match_term.cases.iter() {
            let case_data = case.value();
            self.context().enter_scope(case_data.stack_id.into(), || -> TcResult<_> {
                let subject_ty_copy = self.visitor().copy(match_subject_ty);

                self.in_pat.enter(true, || self.check_node(case_data.bind_pat, subject_ty_copy))?;
                let new_unified_ty =
                    Ty::expect_is(case_data.value, self.visitor().copy(unified_ty));

                if let Some(match_subject_var) = match_subject_var {
                    if let Some(pat_term) = case_data.bind_pat.use_as_non_pat() {
                        self.context().add_assignment(
                            match_subject_var.symbol,
                            subject_ty_copy,
                            pat_term,
                        );
                    }
                }

                match match_annotation_ty {
                    _ if self.is_uninhabitable(subject_ty_copy)? => {
                        let new_unified_ty = self.fresh_meta_for(case_data.value);
                        self.check_node(case_data.value, new_unified_ty)?;
                        self.unify_nodes(new_unified_ty, never_ty(NodeOrigin::Expected))?;
                    }
                    Some(_) => {
                        self.check_node(case_data.value, new_unified_ty)?;
                        if !self.is_uninhabitable(new_unified_ty)? {
                            inhabited.set(true);
                        }
                    }
                    None => {
                        self.check_node(case_data.value, new_unified_ty)?;
                        if !self.is_uninhabitable(new_unified_ty)? {
                            inhabited.set(true);
                            self.unify_nodes(new_unified_ty, unified_ty)?;
                            unified_ty = new_unified_ty;
                        }
                    }
                }

                Ok(())
            })?
        }

        if matches!(*unified_ty.value(), Ty::Meta(_)) {
            if !inhabited.get() {
                unified_ty = never_ty(NodeOrigin::Expected);
            } else {
                unified_ty = Ty::unit_ty(NodeOrigin::Expected);
            }
        }

        self.unify_nodes(unified_ty, annotation_ty)?;

        // @@Caching: Check if the MatchTerm has already been queued for exhaustiveness,
        // if it hasn't, we can use/make a new ExhaustivenessChecker and then
        // add the job.
        let pats =
            match_term.cases.elements().borrow().iter().map(|case| case.bind_pat).collect_vec();
        let mut eck = self.exhaustiveness_checker(match_term.subject);
        self.env.record("exhaustiveness", |_| {
            eck.is_match_exhaustive(&pats, match_subject_ty);
        });
        self.append_exhaustiveness_diagnostics(eck);

        Ok(())
    }

    fn try_normalise(
        &self,
        mut match_term: MatchTerm,
        _: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        let st = NormalisationState::new();
        match_term.subject = self.normalise_node_and_record(match_term.subject, &st)?;

        for case_id in match_term.cases.iter() {
            let case = case_id.value();
            let mut outcome = None;

            self.context().enter_scope(
                case.stack_id.into(),
                || -> Result<(), NormaliseSignal> {
                    match self.match_value_and_get_binds(
                        match_term.subject,
                        case.bind_pat,
                        &mut |name, term_id| self.context().add_untyped_assignment(name, term_id),
                    )? {
                        MatchResult::Successful => {
                            let result = self.normalise_node_and_record(case.value, &st)?;
                            outcome = Some(normalised_to(result));
                        }
                        MatchResult::Failed => {}
                        MatchResult::Stuck => {
                            outcome = Some(stuck_normalising());
                        }
                    }

                    Ok(())
                },
            )?;

            match outcome {
                Some(outcome) => return outcome,
                None => continue,
            }
        }

        panic!("Non-exhaustive match: {}", &match_term)
    }

    fn unify(
        &self,
        src: &mut MatchTerm,
        target: &mut MatchTerm,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        if src.cases.len() != target.cases.len() {
            return self.mismatching_atoms(src_node, target_node);
        }

        for (src_case, target_case) in src.cases.iter().zip(target.cases.iter()) {
            let src_case = src_case.value();
            let target_case = target_case.value();
            self.unify_nodes(src_case.bind_pat, target_case.bind_pat)?;
            self.unify_nodes(src_case.value, target_case.value)?;
        }

        Ok(())
    }
}
