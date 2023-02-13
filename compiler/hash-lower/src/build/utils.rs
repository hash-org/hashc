//! Contains utility functions that perform resolutions on
//! [PatId]s, [TermId]s, [ast::AstNodeId]s. This will read the
//! provided mappings between nodes to locations, patterns, and
//! types.

use hash_ir::{
    ir::{AssertKind, BasicBlock, LocalDecl, Operand, Place, TerminatorKind},
    ty::Mutability,
};
use hash_source::location::Span;
use hash_tir::{pats::PatId, utils::common::CommonUtils};

use super::Builder;

impl<'tcx> Builder<'tcx> {
    /// Get the [Span] of a given [PatId].
    pub(crate) fn span_of_pat(&self, id: PatId) -> Span {
        self.get_location(id).map(|loc| loc.span).unwrap()
    }

    /// Function to create a new [Place] that is used to ignore
    /// the results of expressions, i.e. blocks.
    pub(crate) fn make_tmp_unit(&mut self) -> Place {
        match &self.tmp_place {
            Some(tmp) => *tmp,
            None => {
                let local =
                    LocalDecl::new_auxiliary(self.ctx.tys().common_tys.unit, Mutability::Immutable);
                let local_id = self.declarations.push(local);

                let place = Place::from_local(local_id, self.ctx);
                self.tmp_place = Some(place);
                place
            }
        }
    }

    /// Create an assertion on a particular block
    pub(crate) fn assert(
        &mut self,
        block: BasicBlock,
        condition: Operand,
        expected: bool,
        kind: AssertKind,
        span: Span,
    ) -> BasicBlock {
        let success_block = self.control_flow_graph.start_new_block();

        self.control_flow_graph.terminate(
            block,
            span,
            TerminatorKind::Assert { condition, expected, kind, target: success_block },
        );

        success_block
    }
}
