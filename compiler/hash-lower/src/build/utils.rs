//! Contains utility functions that perform resolutions on
//! [PatId]s, [TermId]s, [ast::AstNodeId]s. This will read the
//! provided mappings between nodes to locations, patterns, and
//! types.

use hash_ir::{
    ir::{AssertKind, BasicBlock, Local, LocalDecl, Operand, Place, TerminatorKind},
    ty::Mutability,
};
use hash_source::{
    identifier::{Identifier, IDENTS},
    location::Span,
};
use hash_tir::{
    environment::env::AccessToEnv, fns::FnDefId, pats::PatId, symbols::Symbol, terms::TermId,
    utils::common::CommonUtils,
};

use super::{Builder, LocalKey};

// @@Temporary: use this for terms that don't have a location
const DUMMY_SPAN: Span = Span::new(0, 0);

impl<'tcx> Builder<'tcx> {
    /// Get the [Span] of a given [PatId].
    pub(crate) fn span_of_pat(&self, id: PatId) -> Span {
        self.get_location(id).map(|loc| loc.span).unwrap_or_else(|| {
            log::info!("expected pattern `{}` to have a location", self.env().with(id));
            DUMMY_SPAN
        })
    }

    /// Get the [Span] of a [FnDefId].
    pub(crate) fn span_of_def(&self, id: FnDefId) -> Span {
        self.get_location(id).map(|loc| loc.span).unwrap_or_else(|| {
            log::info!("expected function definition `{}` to have a location", self.env().with(id));
            DUMMY_SPAN
        })
    }

    /// Get the [Span] of a given [TermId].
    pub(crate) fn span_of_term(&self, id: TermId) -> Span {
        self.get_location(id).map(|loc| loc.span).unwrap_or_else(|| {
            log::info!("expected term `{:?}` to have a location", self.env().with(id));
            DUMMY_SPAN
        })
    }

    /// Create a [LocalKey] from a [Symbol].
    pub(crate) fn local_key_from_symbol(&self, symbol: Symbol) -> LocalKey {
        self.context().get_binding(symbol).kind.into()
    }

    /// Lookup a local by its [LocalKey].
    pub(crate) fn lookup_local(&self, key: &LocalKey) -> Option<Local> {
        self.declaration_map.get(key).copied()
    }

    /// Lookup a [Local] by a specified [Symbol].
    pub(crate) fn lookup_local_symbol(&self, symbol: Symbol) -> Option<Local> {
        let key = self.context().get_binding(symbol).kind.into();
        self.lookup_local(&key)
    }

    /// Get the underlying name for a [Symbol], if the symbol
    /// has no name, then the name is set as `_`.
    pub(crate) fn symbol_name(&self, symbol: Symbol) -> Identifier {
        let data = self.get_symbol(symbol);
        data.name.unwrap_or(IDENTS.underscore)
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
