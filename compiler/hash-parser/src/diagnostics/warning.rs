//! Parser warning definitions.

use std::fmt::Display;

use hash_ast::ast::{Expr, TyParamOrigin};
use hash_reporting::reporter::{Reporter, Reports};
use hash_source::location::Span;
use hash_utils::{derive_more::Constructor, pluralise};

/// Represents a generated warning from within [AstGen][crate::parser::AstGen]
#[derive(Constructor, Debug)]
pub struct ParseWarning {
    /// The kind of warning that is generated, stores relevant information
    /// about the warning.
    kind: WarningKind,

    /// The highlighter span of the where the warning applies to.
    span: Span,
}

/// When warnings describe that a subject could be being applied
/// on a particular kind like `literal` or `block`... etc.
#[derive(Debug, Clone, Copy)]
pub enum SubjectKind {
    /// When the subject is a literal
    Lit,
    /// Block expression kind
    Block,
    /// Default case when the effort is not made to try and
    /// get a specific kind, and where it is possibly unnecessary.
    Expr,
}

impl From<&Expr> for SubjectKind {
    fn from(kind: &Expr) -> Self {
        match kind {
            Expr::Lit(_) => SubjectKind::Lit,
            Expr::Block(_) => SubjectKind::Block,
            _ => SubjectKind::Expr,
        }
    }
}

impl Display for SubjectKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SubjectKind::Lit => write!(f, "literal"),
            SubjectKind::Block => write!(f, "block"),
            SubjectKind::Expr => write!(f, "expression"),
        }
    }
}

#[derive(Debug)]
pub enum WarningKind {
    /// When an expression is wrapped within redundant parentheses.
    RedundantParenthesis(SubjectKind),

    /// When the unary operator `+` is featured, whilst the parser
    /// allows this operator, it has no effect on the expression
    /// and so could be omitted.
    UselessUnaryOperator(SubjectKind),

    /// When the parser encounters a collection of trailing semi-colons
    /// that are unnecessary.
    TrailingSemis(usize),

    /// When type parameters are provided with no specified parameters i.e.
    /// `<>`.
    UselessTyParams { origin: TyParamOrigin },
}

impl From<ParseWarning> for Reports {
    fn from(warning: ParseWarning) -> Self {
        let mut span_label = "".to_string();

        let message = match warning.kind {
            WarningKind::RedundantParenthesis(subject) => {
                format!("unnecessary parentheses around {subject}")
            }
            WarningKind::UselessUnaryOperator(subject) => {
                format!("unary operator `+` has no effect on this {subject}")
            }
            WarningKind::TrailingSemis(length) => {
                span_label = format!(
                    "remove {} semicolon{}",
                    pluralise!("this", length),
                    pluralise!(length)
                );

                format!("unnecessary trailing semicolon{}", pluralise!(length))
            }
            WarningKind::UselessTyParams { origin } => {
                span_label = "remove this `<>`".to_string();

                let label =
                    if matches!(origin, TyParamOrigin::Mod) { "block" } else { "definition" };

                format!("useless type parameters on this `{}` {label}", origin.name())
            }
        };

        let mut reporter = Reporter::new();
        reporter.warning().title(message).add_labelled_span(warning.span, span_label);

        reporter.into_reports()
    }
}
