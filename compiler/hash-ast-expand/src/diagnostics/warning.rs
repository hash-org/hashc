//! Compiler warnings that are emitted during AST expansion.

use derive_more::{Constructor, From};
use hash_ast::ast::AstNodeId;
use hash_attrs::diagnostics::AttrWarning;
use hash_reporting::reporter::{Reporter, Reports};

#[derive(Constructor, Debug)]
pub struct ExpansionWarning {
    /// The kind of error that occurred.
    pub kind: ExpansionWarningKind,

    /// The node that caused the error.
    pub id: AstNodeId,
}

#[derive(Debug, From)]
pub enum ExpansionWarningKind {
    /// Warnings that are generated from the attribute checking phase.
    #[from]
    Attr(AttrWarning),
}

impl From<ExpansionWarning> for Reports {
    fn from(err: ExpansionWarning) -> Self {
        let mut reporter = Reporter::new();
        match err.kind {
            ExpansionWarningKind::Attr(w) => {
                w.add_to_reporter(&mut reporter);
            }
        }

        reporter.into_reports()
    }
}
