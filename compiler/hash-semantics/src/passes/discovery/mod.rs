//! The first pass of the typechecker, which discovers all definitions in
//! the AST and adds them to the stores.

use hash_ast::{
    ast::{self, AstNodeId},
    visitor::AstVisitor,
};
use hash_source::SourceId;
use hash_tir::tir::{NodeOrigin, SymbolId};
use hash_utils::{derive_more::Deref, state::LightState};

use self::defs::DefDiscoveryState;
use super::{analysis_pass::AnalysisPass, ast_info::AstInfo};
use crate::{diagnostics::definitions::SemanticResult, env::SemanticEnv, progress::AnalysisStage};

pub mod defs;
mod discriminants;
pub mod params;
pub mod visitor;

#[derive(Deref)]
pub struct DiscoveryPass<'env, E: SemanticEnv> {
    #[deref]
    env: &'env E,

    /// The name hint for the current definition.
    name_hint: LightState<Option<SymbolId>>,

    /// Keeps track of which definitions have been seen, added, and we are
    /// currently inside.
    def_state: DefDiscoveryState,

    /// The AST info for the current analysis session.
    ast_info: &'env AstInfo,
}

impl<E: SemanticEnv> AnalysisPass for DiscoveryPass<'_, E> {
    type Env = E;
    fn env(&self) -> &Self::Env {
        self.env
    }

    type PassOutput = ();

    fn pass_interactive(
        &self,
        _: SourceId,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> SemanticResult<()> {
        self.visit_body_block(node)
    }

    fn pass_module(
        &self,
        source: SourceId,
        node: ast::AstNodeRef<ast::Module>,
    ) -> SemanticResult<()> {
        debug_assert_eq!(source, node.span().id);
        self.visit_module(node)
    }

    fn pre_pass(&self, source_id: SourceId) -> SemanticResult<Option<()>> {
        if self.get_current_progress(source_id) == AnalysisStage::None {
            self.set_current_progress(source_id, AnalysisStage::Discovery);
            Ok(None)
        } else {
            Ok(Some(()))
        }
    }
}

impl<'env, E: SemanticEnv> DiscoveryPass<'env, E> {
    pub fn new(env: &'env E, ast_info: &'env AstInfo) -> Self {
        Self {
            env,
            name_hint: LightState::new(None),
            def_state: DefDiscoveryState::new(),
            ast_info,
        }
    }

    /// Get the current definition discovery state
    fn def_state(&self) -> &DefDiscoveryState {
        &self.def_state
    }

    /// Take the currently set name hint, or create a new internal name.
    fn take_name_hint_or_create_internal_name(&self, alternative_origin: AstNodeId) -> SymbolId {
        self.name_hint
            .take()
            .unwrap_or_else(|| SymbolId::fresh(NodeOrigin::Given(alternative_origin)))
    }
}
