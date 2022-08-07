//! Hash diagnostic report writing utilities and definitions.
use std::fmt;

use hash_source::SourceMap;

use crate::{
    highlight::{highlight, Modifier},
    report::{Report, ReportElement},
};

/// General data type for displaying [Report]s. This is needed due to the
/// [Report] rendering process needing access to the program modules to get
/// access to the source code.
pub struct ReportWriter<'m> {
    report: Report,
    sources: &'m SourceMap,
}

impl<'m> ReportWriter<'m> {
    pub fn new(report: Report, sources: &'m SourceMap) -> Self {
        Self { report, sources }
    }
}

impl fmt::Display for ReportWriter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Add the optional error code to the general message...
        let error_code_fmt = match self.report.error_code {
            Some(error_code) => highlight(
                self.report.kind.as_colour() | Modifier::Bold,
                format!("[{:0>4}]", error_code.to_num()),
            ),
            None => String::new(),
        };

        // Add the general note about the report...
        writeln!(
            f,
            "{}{}: {}",
            self.report.kind,
            error_code_fmt,
            highlight(Modifier::Bold, &self.report.message),
        )?;

        let longest_indent_width =
            self.report.contents.iter().fold(0, |longest_indent_width, element| match element {
                ReportElement::CodeBlock(code_block) => {
                    code_block.info(self.sources).indent_width.max(longest_indent_width)
                }
                ReportElement::Note(_) => longest_indent_width,
            });

        let mut iter = self.report.contents.iter().peekable();

        while let Some(note) = iter.next() {
            note.render(f, self.sources, longest_indent_width, self.report.kind)?;

            if matches!(iter.peek(), Some(ReportElement::CodeBlock(_))) {
                writeln!(f)?;
            }
        }

        Ok(())
    }
}
