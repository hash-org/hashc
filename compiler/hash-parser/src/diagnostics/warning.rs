//! Parser warning definitions.
#![allow(unused, dead_code)]

use derive_more::Constructor;
use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind},
};
use hash_source::location::SourceLocation;

/// Represents a generated warning from within [AstGen]
#[derive(Constructor)]
pub struct ParseWarning {
    /// The kind of warning that is generated, stores relevant information
    /// about the warning
    kind: WarningKind,
    location: SourceLocation,
}

pub enum WarningKind {
    RedundantParenthesis,
}

impl From<ParseWarning> for Report {
    fn from(warning: ParseWarning) -> Self {
        let mut builder = ReportBuilder::new();

        let message = match warning.kind {
            WarningKind::RedundantParenthesis => "unnecessary parentheses around expression",
        };

        builder
            .with_kind(ReportKind::Warning)
            .with_message(message)
            .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(warning.location, "here")));

        builder.build()
    }
}
