use core::fmt;
use std::{
    cell::Cell,
    iter::{once, repeat},
};

use hash_ast::{location::SourceLocation, module::Modules};

use crate::{
    errors::ErrorCode,
    highlight::{highlight, Colour, Modifier},
};

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ReportKind {
    Error,
    Info,
    Warning,
}

impl ReportKind {
    fn as_colour(&self) -> Colour {
        match self {
            ReportKind::Error => Colour::Red,
            ReportKind::Info => Colour::Blue,
            ReportKind::Warning => Colour::Yellow,
        }
    }

    fn message(&self) -> &'static str {
        match self {
            ReportKind::Error => "error",
            ReportKind::Info => "info",
            ReportKind::Warning => "warn",
        }
    }
}

impl fmt::Display for ReportKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            highlight(self.as_colour() | Modifier::Bold, self.message())
        )
    }
}

#[derive(Debug)]
pub struct ReportNote {
    pub label: String,
    pub message: String,
}

impl ReportNote {
    pub fn new(label: impl ToString, message: impl ToString) -> Self {
        Self {
            label: label.to_string(),
            message: message.to_string(),
        }
    }

    fn render(&self, f: &mut fmt::Formatter<'_>, longest_indent_width: usize) -> fmt::Result {
        writeln!(
            f,
            "{} = {}: {}",
            " ".repeat(longest_indent_width),
            highlight(Modifier::Bold, &self.label),
            self.message
        )?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct ReportCodeBlock {
    pub source_location: SourceLocation,
    pub code_message: String,
    info: Cell<Option<ReportCodeBlockInfo>>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct ReportCodeBlockInfo {
    pub indent_width: usize,
    pub start_col: usize,
    pub start_row: usize,
    pub end_col: usize,
    pub end_row: usize,
}

fn offset_col_row(offset: usize, source: &str) -> (usize, usize) {
    let source_lines = source.split('\n');

    let mut bytes_skipped = 0;
    let mut total_lines: usize = 0;
    let mut last_line_len = 0;

    let mut line_index = None;
    for (line_idx, line) in source_lines.enumerate() {
        // One byte for the newline
        let skip_width = line.len() + 1;

        if (bytes_skipped..=bytes_skipped + skip_width).contains(&offset) {
            line_index = Some((offset - bytes_skipped, line_idx));
            break;
        }

        bytes_skipped += skip_width;
        total_lines += 1;
        last_line_len = line.len();
    }

    line_index.unwrap_or((
        last_line_len.saturating_sub(1),
        total_lines.saturating_sub(1),
    ))
}

impl ReportCodeBlock {
    pub fn new(source_location: SourceLocation, code_message: impl ToString) -> Self {
        Self {
            source_location,
            code_message: code_message.to_string(),
            info: Cell::new(None),
        }
    }

    // Get the indent widths of this code block as (outer, inner).
    fn info(&self, modules: &Modules) -> ReportCodeBlockInfo {
        match self.info.get() {
            Some(info) => info,
            None => {
                let module = modules.get_by_index(self.source_location.module_index);
                let source = module.content();

                let location = self.source_location.location;

                let (start_col, start_row) = offset_col_row(location.start(), source);
                let (end_col, end_row) = offset_col_row(location.end(), source);

                let indent_width = (start_row + 1).max(end_row + 1).to_string().chars().count();

                let info = ReportCodeBlockInfo {
                    indent_width,
                    start_col,
                    start_row,
                    end_col,
                    end_row,
                };

                self.info.replace(Some(info));
                info
            }
        }
    }

    fn render(
        &self,
        f: &mut fmt::Formatter,
        modules: &Modules,
        longest_indent_width: usize,
        report_kind: ReportKind,
    ) -> fmt::Result {
        // Print line numbers, separator, then the code itself, split by newlines
        // Should put the code_message where it is supposed to be with a caret (^) followed by (_)
        // or equivalent unicode character.
        //
        // Print a few lines before and after location/code_message.
        let module = modules.get_by_index(self.source_location.module_index);
        let source = module.content();
        let ReportCodeBlockInfo {
            start_row,
            end_row,
            start_col,
            end_col,
            ..
        } = self.info(modules);

        const MAX_BUFFER: usize = 5;
        let top_buffer: usize = (end_row - start_row + 1).min(MAX_BUFFER);
        let bottom_buffer: usize = (end_row - start_row + 1).min(MAX_BUFFER);

        const ERROR_MARKING_CHAR: &str = "^";

        let error_view = source
            .trim_end_matches('\n')
            .split('\n')
            .enumerate()
            .skip(start_row.saturating_sub(top_buffer))
            .take(top_buffer + end_row - start_row + 1 + bottom_buffer);

        writeln!(
            f,
            "{}--> {}",
            " ".repeat(longest_indent_width),
            highlight(
                Modifier::Underline,
                format!(
                    "{}:{}:{}",
                    module.filename().to_string_lossy(),
                    start_row + 1,
                    start_col + 1,
                )
            )
        )?;
        for (index, line) in error_view {
            let index_str = format!(
                "{:>pad_width$}",
                index + 1,
                pad_width = longest_indent_width
            );
            writeln!(
                f,
                "{} |   {}",
                if (start_row..=end_row).contains(&index) {
                    highlight(report_kind.as_colour(), &index_str)
                } else {
                    index_str
                },
                line
            )?;

            if (start_row..=end_row).contains(&index) && !line.is_empty() {
                let dashes = repeat(ERROR_MARKING_CHAR).take(
                    if index == start_row && start_row == end_row {
                        end_col - start_col
                    } else if index == start_row {
                        line.len().saturating_sub(start_col)
                    } else if index == end_row {
                        end_col
                    } else {
                        line.len()
                    },
                );

                let mut code_note: String = repeat(" ")
                    .take(if index == start_row { start_col } else { 0 })
                    .chain(dashes)
                    .collect();

                if index == end_row {
                    code_note.extend(once(" ").chain(once(self.code_message.as_str())));
                }

                writeln!(
                    f,
                    "{} |   {}",
                    " ".repeat(longest_indent_width),
                    highlight(report_kind.as_colour(), &code_note)
                )?;
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
pub enum ReportElement {
    CodeBlock(ReportCodeBlock),
    Note(ReportNote),
}

impl ReportElement {
    fn render(
        &self,
        f: &mut fmt::Formatter,
        modules: &Modules,
        longest_indent_width: usize,
        report_kind: ReportKind,
    ) -> fmt::Result {
        match self {
            ReportElement::CodeBlock(code_block) => {
                code_block.render(f, modules, longest_indent_width, report_kind)
            }
            ReportElement::Note(note) => note.render(f, longest_indent_width),
        }
    }
}

#[derive(Debug)]
pub struct Report {
    pub kind: ReportKind,
    pub message: String,
    pub error_code: Option<ErrorCode>,
    pub contents: Vec<ReportElement>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct IncompleteReportError;

impl std::error::Error for IncompleteReportError {}
impl fmt::Display for IncompleteReportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "incomplete report, cannot build")
    }
}

#[derive(Debug, Default)]
pub struct ReportBuilder {
    kind: Option<ReportKind>,
    message: Option<String>,
    error_code: Option<ErrorCode>,
    contents: Vec<ReportElement>,
}

impl ReportBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_message(&mut self, message: impl ToString) -> &mut Self {
        self.message = Some(message.to_string());
        self
    }

    pub fn with_kind(&mut self, kind: ReportKind) -> &mut Self {
        self.kind = Some(kind);
        self
    }

    pub fn with_error_code(&mut self, error_code: ErrorCode) -> &mut Self {
        self.error_code = Some(error_code);
        self
    }

    pub fn add_element(&mut self, element: ReportElement) -> &mut Self {
        self.contents.push(element);
        self
    }

    pub fn build(&mut self) -> Result<Report, IncompleteReportError> {
        Ok(Report {
            kind: self.kind.take().ok_or(IncompleteReportError)?,
            message: self.message.take().ok_or(IncompleteReportError)?,
            error_code: self.error_code.take(),
            contents: std::mem::replace(&mut self.contents, vec![]),
        })
    }
}

pub struct ReportWriter<'c, 'm> {
    report: Report,
    modules: &'m Modules<'c>,
}

impl<'c, 'm> ReportWriter<'c, 'm> {
    pub fn new(report: Report, modules: &'m Modules<'c>) -> Self {
        Self { report, modules }
    }
}

impl fmt::Display for ReportWriter<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let error_code_fmt = match self.report.error_code {
            Some(error_code) => highlight(
                self.report.kind.as_colour() | Modifier::Bold,
                format!("[{}]", error_code),
            ),
            None => String::new(),
        };
        writeln!(
            f,
            "{}{}: {}",
            self.report.kind,
            error_code_fmt,
            highlight(Modifier::Bold, &self.report.message),
        )?;

        let longest_indent_width =
            self.report
                .contents
                .iter()
                .fold(0, |longest_indent_width, element| match element {
                    ReportElement::CodeBlock(code_block) => code_block
                        .info(self.modules)
                        .indent_width
                        .max(longest_indent_width),
                    ReportElement::Note(_) => longest_indent_width,
                });

        let mut iter = self.report.contents.iter().peekable();

        loop {
            match iter.next() {
                Some(note) => {
                    note.render(f, self.modules, longest_indent_width, self.report.kind)?;

                    if matches!(iter.peek(), Some(ReportElement::CodeBlock(_))) {
                        writeln!(f, "")?;
                    }
                }
                None => break,
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use hash_alloc::{row, Castle};
    use hash_ast::{ast, location::Location, module::ModuleBuilder};

    use super::*;

    #[test]
    fn reporting_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        let builder = ModuleBuilder::new();

        let path = PathBuf::from("./../../examples/prelude.hash");
        let contents = std::fs::read_to_string(&path).unwrap();
        let test_idx = builder.reserve_index();

        builder.add_contents(test_idx, path, contents);
        builder.add_module_at(
            test_idx,
            ast::Module {
                contents: row![&wall],
            },
        );

        let modules = builder.build();

        let report = ReportBuilder::new()
            .with_message("Bro what you wrote here is wrong.")
            .with_kind(ReportKind::Error)
            .with_error_code(ErrorCode::Parsing)
            .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                SourceLocation {
                    location: Location::span(10223, 10224),
                    module_index: test_idx,
                },
                "don't be crazy.",
            )))
            .add_element(ReportElement::Note(ReportNote::new(
                "note",
                "You really are a dummy.",
            )))
            .build()
            .unwrap();

        let report_writer = ReportWriter::new(report, &modules);

        println!("{}", report_writer);
    }

    #[test]
    fn offset_test() {
        let contents = "Hello, world!\nGoodbye, world, it has been fun.";

        let (col, row) = offset_col_row(contents.len() - 1, contents);
        assert_eq!((col, row), (31, 1));

        let (col, row) = offset_col_row(contents.len() + 3, contents);
        assert_eq!((col, row), (31, 1));
    }
}
