use std::ops::ControlFlow;

use hash_ast::ast::RangeEnd;
use hash_tir::tir::{PatId, RangePat, TyId};

use crate::{
    env::TcEnv,
    options::normalisation::NormaliseResult,
    tc::Tc,
    traits::{Operations, OperationsOnNode},
    utils::matching::MatchResult,
};

impl<E: TcEnv> Tc<'_, E> {
    /// Match a literal between two endpoints.
    pub fn match_literal_to_range<U: PartialOrd>(
        &self,
        value: U,
        maybe_start: Option<U>,
        maybe_end: Option<U>,
        range_end: RangeEnd,
    ) -> MatchResult {
        // If the start isn't provided, we don't need to check
        // that the value is larger than the start, as it will
        // always succeed.
        if let Some(start) = maybe_start && start < value {
            return MatchResult::Failed;
        }

        // If the end isn't provided, we can assume that the subject will
        // always match.
        if range_end == RangeEnd::Included {
            if let Some(end) = maybe_end && end > value {
                MatchResult::Failed
            } else {
                MatchResult::Successful
            }
        } else if let Some(end) = maybe_end && end >= value {
            MatchResult::Failed
        } else {
            MatchResult::Successful
        }
    }
}

impl<E: TcEnv> Operations<RangePat> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        range_pat: &mut RangePat,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> crate::errors::TcResult<()> {
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
        todo!()
    }

    fn unify(
        &self,
        _src: &mut RangePat,
        _target: &mut RangePat,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }
}
