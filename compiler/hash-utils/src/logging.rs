//! Hash compiler logging utilities. This defines a simple logger with a
//! style which should be used across the compiler to log and print messages.

use std::{
    collections::BTreeMap,
    io::{self, Write},
};

use once_cell::sync::OnceCell;

use crate::{
    highlight::{highlight, Colour, Modifier},
    log::{
        kv::{Error, Key, Value, Visitor},
        Level, Log, Metadata, Record,
    },
    stream::CompilerOutputStream,
    stream_writeln,
};

#[derive(Default, PartialEq, Eq, Clone, Copy, Debug)]
pub enum LoggingFormat {
    /// Use the default logging format.
    #[default]
    Default,

    /// Use the JSON logging format.
    Json,
}

/// The compiler logger that is used by the compiler for `log!` statements.
///
/// This is also used to emit structured messages to the user.
#[derive(Default, Debug)]
pub struct CompilerLogger {
    /// The output stream that the logger will write to.
    pub output_stream: OnceCell<CompilerOutputStream>,

    /// The error stream that the logger will write to.
    pub error_stream: OnceCell<CompilerOutputStream>,

    /// The format to use when logging information.
    logging_format: OnceCell<LoggingFormat>,
}

impl CompilerLogger {
    /// Create a new compiler logger.
    pub const fn new() -> Self {
        Self {
            output_stream: OnceCell::new(),
            error_stream: OnceCell::new(),
            logging_format: OnceCell::new(),
        }
    }

    /// Create a new [CompilerLogger] with a JSON logging format.
    pub fn with_json_format(&self) {
        self.logging_format.set(LoggingFormat::Json).unwrap();
    }

    /// Log the given record in the JSON format.
    fn log_json(&self, out: &mut dyn Write, record: &Record, _: String) -> io::Result<()> {
        let kvs = record.key_values();
        let mut visitor = LoggerVisitor::default();
        kvs.visit(&mut visitor).unwrap();

        writeln!(out, "{}", serde_json::to_string(&visitor.0).unwrap())
    }

    fn log_default(&self, out: &mut dyn Write, record: &Record, level_prefix: String) {
        stream_writeln!(
            out,
            "{level_prefix}: {message}",
            level_prefix = level_prefix,
            message = record.args()
        );
    }
}

impl Log for CompilerLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= Level::Debug
    }

    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }

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

        if *self.logging_format.get().unwrap() == LoggingFormat::Json {
            self.log_json(&mut out, record, level_prefix).unwrap();
        } else {
            self.log_default(&mut out, record, level_prefix);
        }
    }

    fn flush(&self) {}
}

#[derive(Default)]
struct LoggerVisitor<'l>(BTreeMap<Key<'l>, Value<'l>>);

impl<'l> Visitor<'l> for LoggerVisitor<'l> {
    fn visit_pair(&mut self, key: Key<'l>, value: Value<'l>) -> Result<(), Error> {
        self.0.insert(key, value);
        Ok(())
    }
}
