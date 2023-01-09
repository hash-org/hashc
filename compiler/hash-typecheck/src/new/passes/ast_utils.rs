use hash_ast::{
    ast::{AstNodeRef, BodyBlock, Module, OwnsAstNode},
    node_map::SourceRef,
};
use hash_source::location::{SourceLocation, Span};

use crate::new::{
    diagnostics::error::TcResult, environment::tc_env::AccessToTcEnv, ops::common::CommonOps,
};

pub trait AstPass: AccessToTcEnv {
    fn pass_interactive(&self, node: AstNodeRef<BodyBlock>) -> TcResult<()>;
    fn pass_module(&self, node: AstNodeRef<Module>) -> TcResult<()>;

    fn pass_source(&self) {
        let source = self.node_map().get_source(self.current_source_info().source_id);
        let result = match source {
            SourceRef::Interactive(interactive_source) => {
                self.pass_interactive(interactive_source.node_ref())
            }
            SourceRef::Module(module_source) => self.pass_module(module_source.node_ref()),
        };
        self.tc_env().try_or_add_error(result);
    }
}

pub trait AstUtils: AccessToTcEnv {
    /// Create a [SourceLocation] from a [Span].
    fn source_location(&self, span: Span) -> SourceLocation {
        SourceLocation { span, id: self.current_source_info().source_id }
    }

    /// Create a [SourceLocation] at the given [hash_ast::ast::AstNode].
    fn node_location<N>(&self, node: AstNodeRef<N>) -> SourceLocation {
        let node_span = node.span();
        self.source_location(node_span)
    }

    /// Unwrap a [`TcResult`] or add the error to the diagnostics.
    fn unwrap_or_diagnostic<T>(&self, result: TcResult<T>) -> Option<T> {
        match result {
            Ok(ok) => Some(ok),
            Err(err) => {
                self.diagnostics().add_error(err);
                None
            }
        }
    }
}
