use std::ops::ControlFlow;

use hash_ast::ast::RangeEnd;
use hash_const_eval::{eval::ConstFolder, op::BinOp};
use hash_repr::constant::Const;
use hash_source::constant::Scalar;
use hash_tir::tir::{PatId, RangePat, TyId};

use crate::{
    env::TcEnv,
    options::normalisation::{NormaliseResult, normalise_nested},
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode},
    utils::matching::MatchResult,
};

impl<E: TcEnv> Tc<'_, E> {
    /// Match a literal between two endpoints.
    pub fn match_literal_to_range(
        &self,
        value: Const,
        maybe_start: Option<Const>,
        maybe_end: Option<Const>,
        range_end: RangeEnd,
    ) -> MatchResult {
        let eval = ConstFolder::new(self.layout_computer());

        let result_is_true = |maybe_value: Option<Const>| {
            if let Some(value) = maybe_value {
                value.as_scalar() == Scalar::TRUE
            } else {
                // @@Investigate: should this be a hard error?
                debug_assert!(false, "Failed to evaluate constant operation");
                false
            }
        };

        // If the start isn't provided, we don't need to check
        // that the value is larger than the start, as it will
        // always succeed.
        if let Some(start) = maybe_start
            && result_is_true(eval.try_fold_bin_op(BinOp::Lt, &start, &value))
        {
            return MatchResult::Failed;
        }

        // If the end isn't provided, we can assume that the subject will
        // always match.
        if range_end == RangeEnd::Included {
            if let Some(end) = maybe_end
                && result_is_true(eval.try_fold_bin_op(BinOp::Gt, &end, &value))
            {
                MatchResult::Failed
            } else {
                MatchResult::Successful
            }
        } else if let Some(end) = maybe_end
            && result_is_true(eval.try_fold_bin_op(BinOp::GtEq, &end, &value))
        {
            MatchResult::Failed
        } else {
            MatchResult::Successful
        }
    }
}

impl<E: TcEnv> OperationsOn<RangePat> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        range_pat: &mut RangePat,
        annotation_ty: Self::AnnotNode,
        _: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        let RangePat { lo, hi, .. } = range_pat;

        lo.map(|lo| self.check_node(*lo, annotation_ty)).transpose()?;
        hi.map(|hi| self.check_node(*hi, annotation_ty)).transpose()?;

        Ok(())
    }

    fn try_normalise(
        &self,
        _item: RangePat,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        normalise_nested()
    }

    fn unify(
        &self,
        _: &mut RangePat,
        _: &mut RangePat,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        // @@Todo: unification of range patterns
        self.mismatching_atoms(src_node, target_node)
    }
}
