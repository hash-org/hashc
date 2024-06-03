//! Hash compiler logging utilities. This defines a simple logger with a
//! style which should be used across the compiler to log and print messages.

use std::io::Write;

use once_cell::sync::OnceCell;

use crate::{
    highlight::{highlight, Colour, Modifier},
    log::{Level, Log, Metadata, Record},
    stream::CompilerOutputStream,
    stream_writeln,
};

/// The compiler logger that is used by the compiler for `log!` statements.
///
/// This is also used to emit structured messages to the user.
#[derive(Default)]
pub struct CompilerLogger {
    /// The output stream that the logger will write to.
    pub output_stream: OnceCell<CompilerOutputStream>,

    /// The error stream that the logger will write to.
    pub error_stream: OnceCell<CompilerOutputStream>,
}

impl CompilerLogger {
    /// Create a new compiler logger.
    pub const fn new() -> Self {
        Self { output_stream: OnceCell::new(), error_stream: OnceCell::new() }
    }
}

impl Log for CompilerLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= Level::Debug
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            // Custom colour formatting for the log level
            let level_prefix = match record.level() {
                Level::Error => highlight(Colour::Red | Modifier::Bold, "error"),
                Level::Warn => highlight(Colour::Yellow | Modifier::Bold, "warn"),
                Level::Info => highlight(Colour::Blue | Modifier::Bold, "info"),
                Level::Debug => highlight(Colour::Blue | Modifier::Bold, "debug"),
                Level::Trace => highlight(Colour::Magenta | Modifier::Bold, "trace"),
            };

            let mut out = if record.level() == Level::Error {
                self.error_stream.get().unwrap().clone()
            } else {
                self.output_stream.get().unwrap().clone()
            };

            stream_writeln!(
                out,
                "{level_prefix}: {message}",
                level_prefix = level_prefix,
                message = record.args()
            );
        }
    }

    fn flush(&self) {}
}
