//! Hash diagnostic report writing utilities and definitions.
use std::fmt;

use hash_source::SourceMapUtils;
use hash_utils::highlight::{highlight, Modifier};

use crate::{
    report::{Report, ReportElement},
    reporter::Reports,
};

/// General data type for displaying [Report]s. This is needed due to the
/// [Report] rendering process needing access to the program modules to get
/// access to the source code.
pub struct ReportWriter {
    reports: Reports,
}

impl ReportWriter {
    pub fn new(reports: Reports) -> Self {
        Self { reports }
    }
    pub fn single(report: Report) -> Self {
        Self { reports: vec![report] }
    }
}

impl fmt::Display for ReportWriter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for report in &self.reports {
            // Add the optional error code to the general message...
            let error_code_fmt = match report.error_code {
                Some(error_code) => highlight(
                    report.kind.as_colour() | Modifier::Bold,
                    format!("[{:0>4}]", error_code.to_num()),
                ),
                None => String::new(),
            };

            // Add the general note about the report...
            writeln!(
                f,
                "{}{}: {}",
                report.kind,
                error_code_fmt,
                highlight(Modifier::Bold, &report.title),
            )?;

            let longest_indent_width =
                report.contents.iter().fold(0, |longest_indent_width, element| match element {
                    ReportElement::CodeBlock(code_block) => {
                        SourceMapUtils::map(code_block.span.id, |source| {
                            code_block.info(source).indent_width.max(longest_indent_width)
                        })
                    }
                    ReportElement::Note(_) => longest_indent_width,
                });

            let mut iter = report.contents.iter().peekable();

            while let Some(note) = iter.next() {
                note.render(f, longest_indent_width, report.kind)?;

                if matches!(iter.peek(), Some(ReportElement::CodeBlock(_))) {
                    writeln!(f)?;
                }
            }
        }
        Ok(())
    }
}
