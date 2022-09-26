//! Parser warning definitions.
#![allow(unused, dead_code)]

use std::fmt::Display;

use derive_more::Constructor;
use hash_ast::ast::Expr;
use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind},
};
use hash_source::{
    location::{SourceLocation, Span},
    SourceId,
};
use hash_utils::pluralise;

use crate::parser::DefinitionKind;

/// Represents a generated warning from within [AstGen][crate::parser::AstGen]
#[derive(Constructor, Debug)]
pub struct ParseWarning {
    /// The kind of warning that is generated, stores relevant information
    /// about the warning.
    kind: WarningKind,
    /// The highlighter span of the where the warning applies to.
    location: Span,
}

/// When warnings describe that a subject could be being applied
/// on a particular kind like `literal` or `block`... etc.
#[derive(Debug)]
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
            Expr::LitExpr(_) => SubjectKind::Lit,
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

    UselessTyParams {
        def_kind: DefinitionKind,
    },
}

pub(crate) struct ParseWarningWrapper(pub ParseWarning, pub SourceId);

impl From<ParseWarningWrapper> for Report {
    fn from(ParseWarningWrapper(warning, id): ParseWarningWrapper) -> Self {
        let mut builder = ReportBuilder::new();
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
            WarningKind::UselessTyParams { def_kind } => {
                span_label = "remove this `<>`".to_string();

                let label = if matches!(def_kind, DefinitionKind::Mod | DefinitionKind::Mod) {
                    "block"
                } else {
                    "definition"
                };

                format!("useless type parameters on this `{def_kind}` {label}")
            }
        };

        builder.with_kind(ReportKind::Warning).with_message(message).add_element(
            ReportElement::CodeBlock(ReportCodeBlock::new(
                SourceLocation { span: warning.location, id },
                span_label,
            )),
        );

        builder.build()
    }
}
