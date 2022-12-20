use hash_ast::ast::AstNodeRef;
use hash_source::location::{SourceLocation, Span};

use crate::new::environment::tc_env::AccessToTcEnv;

pub trait AstOps: AccessToTcEnv {
    /// Create a [SourceLocation] from a [Span].
    fn source_location(&self, span: Span) -> SourceLocation {
        SourceLocation { span, id: self.current_source_info().source_id }
    }

    /// Create a [SourceLocation] at the given [hash_ast::ast::AstNode].
    fn node_location<N>(&self, node: AstNodeRef<N>) -> SourceLocation {
        let node_span = node.span();
        self.source_location(node_span)
    }
}

impl<T: AccessToTcEnv> AstOps for T {}
