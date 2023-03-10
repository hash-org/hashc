//! Contains operations that are common during typechecking and don't fit
//! anywhere else.

use hash_reporting::diagnostic::Diagnostics;
use hash_tir::ast_info::AstInfo;

use crate::{
    diagnostics::error::SemanticResult,
    environment::{analysis_progress::AnalysisStage, sem_env::AccessToSemEnv},
};

pub trait CommonOps: AccessToSemEnv {
    /// If the result is an error, add it to the diagnostics and return `None`.
    fn try_or_add_error<T>(&self, result: SemanticResult<T>) -> Option<T> {
        match result {
            Ok(t) => Some(t),
            Err(error) => {
                self.diagnostics().add_error(error);
                None
            }
        }
    }

    fn ast_info(&self) -> &AstInfo {
        self.stores().ast_info()
    }

    fn set_current_progress(&self, stage: AnalysisStage) {
        self.analysis_progress().set(self.current_source_info().source_id(), stage);
    }

    fn get_current_progress(&self) -> AnalysisStage {
        self.analysis_progress().get(self.current_source_info().source_id())
    }
}

impl<T: AccessToSemEnv> CommonOps for T {}
