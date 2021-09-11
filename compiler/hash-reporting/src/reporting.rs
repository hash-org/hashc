use core::fmt;
use std::iter::{self, once, repeat};

use hash_ast::{
    location::{Location, SourceLocation},
    module::Modules,
};

use crate::highlight::{highlight, Colour, Modifier};

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ErrorCode {
    Parsing,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ReportKind {
    Error,
    Info,
    Warning,
}

impl fmt::Display for ReportKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ReportKind::Error => highlight(Colour::Red | Modifier::Bold, "error"),
                ReportKind::Info => highlight(Colour::Blue | Modifier::Bold, "info"),
                ReportKind::Warning => highlight(Colour::Yellow | Modifier::Bold, "warn"),
            }
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
}

#[derive(Debug)]
pub struct Report {
    pub kind: ReportKind,
    pub message: String,
    pub error_code: ErrorCode,

    pub location: SourceLocation,
    pub code_message: String,

    pub additional_notes: Vec<ReportNote>,
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
    location: Option<SourceLocation>,
    code_message: Option<String>,
    additional_notes: Vec<ReportNote>,
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

    pub fn with_location(&mut self, location: SourceLocation) -> &mut Self {
        self.location = Some(location);
        self
    }

    pub fn with_code_message(&mut self, code_message: impl ToString) -> &mut Self {
        self.code_message = Some(code_message.to_string());
        self
    }

    pub fn add_note(&mut self, note: ReportNote) -> &mut Self {
        self.additional_notes.push(note);
        self
    }

    pub fn build(&mut self) -> Result<Report, IncompleteReportError> {
        Ok(Report {
            kind: self.kind.take().ok_or(IncompleteReportError)?,
            message: self.message.take().ok_or(IncompleteReportError)?,
            error_code: self.error_code.take().ok_or(IncompleteReportError)?,
            location: self.location.take().ok_or(IncompleteReportError)?,
            code_message: self.code_message.take().ok_or(IncompleteReportError)?,
            additional_notes: std::mem::replace(&mut self.additional_notes, vec![]),
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

fn offset_col_row(offset: usize, source: &str) -> (usize, usize) {
    let source_lines = source.split('\n');

    let mut bytes_skipped = 0;
    let mut total_lines = 0;
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
        (last_line_len as isize - 1).max(0) as usize,
        (total_lines as isize - 1).max(0) as usize,
    ))
}

impl fmt::Display for ReportWriter<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}: {}", self.report.kind, self.report.message)?;

        // Print line numbers, separator, then the code itself, split by newlines
        // Should put the code_message where it is supposed to be with a caret (^) followed by (_)
        // or equivalent unicode character.
        //
        // Print a few lines before and after location/code_message.

        let module = self.modules.get_by_index(self.report.location.module_index);
        let source = module.content();

        const TOP_BUFFER: usize = 3;
        const BOTTOM_BUFFER: usize = 4;

        const ERROR_MARKING_CHAR: &str = "^";

        let location = self.report.location.location;

        let (start_col, start_row) = offset_col_row(location.start(), source);
        let (end_col, end_row) = offset_col_row(location.end(), source);

        // @@Todo: calculate from file size
        let outer_indent_width = (start_row + 1).max(end_row + 1).to_string().chars().count();
        let inner_indent_width = 2;

        let error_view = source
            .trim_end_matches('\n')
            .split('\n')
            .enumerate()
            .skip((start_row as isize - TOP_BUFFER as isize).max(0) as usize)
            .take(end_row - start_row + TOP_BUFFER + BOTTOM_BUFFER);

        writeln!(
            f,
            "{}",
            highlight(
                Modifier::Bold,
                format!(
                    "{}--> {}:{}:{}",
                    " ".repeat(outer_indent_width),
                    module.filename().to_string_lossy(),
                    start_row + 1,
                    start_col + 1,
                )
            )
        )?;
        for (index, line) in error_view {
            let index_str = format!("{:>pad_width$}", index + 1, pad_width = outer_indent_width);
            writeln!(
                f,
                "{} | {}{}",
                if (start_row..=end_row).contains(&index) {
                    highlight(Colour::Red, &index_str)
                } else {
                    index_str
                },
                " ".repeat(inner_indent_width),
                line
            )?;

            if (start_row..=end_row).contains(&index) {
                let dashes = repeat(ERROR_MARKING_CHAR).take(
                    if index == start_row && start_row == end_row {
                        end_col - start_col
                    } else if index == start_row {
                        line.len() - start_col
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
                    code_note.extend(once(" ").chain(once(self.report.code_message.as_str())));
                }

                writeln!(
                    f,
                    "{} | {}{}",
                    " ".repeat(outer_indent_width),
                    " ".repeat(inner_indent_width),
                    highlight(Colour::Red, &code_note)
                )?;
            }
        }

        // Notes
        for note in &self.report.additional_notes {
            writeln!(
                f,
                "{} = {}: {}",
                " ".repeat(outer_indent_width),
                highlight(Modifier::Bold, &note.label),
                note.message
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use hash_alloc::{row, Castle};
    use hash_ast::{ast, module::ModuleBuilder};

    use super::*;

    #[test]
    fn reporting_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        let builder = ModuleBuilder::new();

        let path = PathBuf::from("/Users/constantine/Git/hash-org/lang/examples/prelude.hash");
        let contents = std::fs::read_to_string(&path).unwrap();
        let test_idx = builder.reserve_index();
        builder.add_module_at(
            test_idx,
            path,
            contents,
            ast::Module {
                contents: row![&wall],
            },
        );

        let modules = builder.build();

        let report = ReportBuilder::new()
            .with_message("Bro what you wrote here is wrong.")
            .with_location(SourceLocation {
                location: Location::span(10000, 10223),
                module_index: test_idx,
            })
            .with_code_message("don't be crazy.")
            .with_kind(ReportKind::Error)
            .with_error_code(ErrorCode::Parsing)
            .add_note(ReportNote::new("note", "You really are a dummy."))
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
