use std::cell::Cell;

use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_tir::{
    intrinsics::definitions::never_ty,
    tir::{MatchTerm, NodeOrigin, NodesId, Term, TermId, Ty, TyId},
    visitor::{Map, Visitor},
};
use itertools::Itertools;

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::TcResult,
    operations::{Operations, OperationsOnNode},
};

impl<E: TcEnv> Operations<MatchTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        match_term: &mut MatchTerm,
        annotation_ty: Self::TyNode,
        _original_node_id: Self::Node,
    ) -> crate::errors::TcResult<()> {
        self.check_ty(annotation_ty)?;
        let match_subject_ty = Ty::hole_for(match_term.subject);
        self.check_node(match_term.subject, match_subject_ty)?;

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
                let subject_ty_copy = Visitor::new().copy(match_subject_ty);

                self.infer_pat(case_data.bind_pat, subject_ty_copy, Some(match_term.subject))?;
                let new_unified_ty =
                    Ty::expect_is(case_data.value, Visitor::new().copy(unified_ty));

                if let Some(match_subject_var) = match_subject_var {
                    if let Some(pat_term) = case_data.bind_pat.try_use_as_term() {
                        self.context().add_assignment(
                            match_subject_var.symbol,
                            subject_ty_copy,
                            pat_term,
                        );
                    }
                }

                match match_annotation_ty {
                    _ if self.uni_ops().is_uninhabitable(subject_ty_copy)? => {
                        let new_unified_ty = Ty::hole_for(case_data.value);
                        self.check_node(case_data.value, new_unified_ty)?;
                        self.check_by_unify(new_unified_ty, never_ty(NodeOrigin::Expected))?;
                    }
                    Some(_) => {
                        self.check_node(case_data.value, new_unified_ty)?;
                        if !self.uni_ops().is_uninhabitable(new_unified_ty)? {
                            inhabited.set(true);
                        }
                    }
                    None => {
                        self.check_node(case_data.value, new_unified_ty)?;
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
        let mut eck = self.exhaustiveness_checker(match_term.subject);
        self.env.time_item("exhaustiveness", |_| {
            eck.is_match_exhaustive(&pats, match_subject_ty);
        });
        self.append_exhaustiveness_diagnostics(eck);

        Ok(())
    }

    fn normalise(
        &self,
        _opts: &crate::operations::normalisation::NormalisationOptions,
        _item: MatchTerm,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: &mut MatchTerm,
        _target: &mut MatchTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut MatchTerm) {
        todo!()
    }
}
