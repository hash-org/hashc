//! Hash compiler logging utilities. This defines a simple logger with a
//! style which should be used across the compiler to log and print messages.

use std::{
    collections::BTreeMap,
    fmt,
    io::{self, Write},
};

use clap::ValueEnum;
use once_cell::sync::OnceCell;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::{
    highlight::{Colour, Modifier, highlight},
    log::{
        Level, Log, Metadata, Record,
        kv::{Error, Key, Value, Visitor},
    },
    stream::CompilerOutputStream,
    stream_writeln,
};

/// The [CompilerMessagingFormat] specifies the message mode that the compiler
/// will use to to emit and receive messages.
#[derive(
    ValueEnum, Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize, JsonSchema, Default,
)]
#[serde(rename_all = "lowercase")]
pub enum CompilerMessagingFormat {
    /// All messages that are emitted to and from the compiler will be in JSON
    /// format according to the schema that represents [CompilerMessage].
    Json,

    /// Normal mode is the classic emission of messages as the compiler would
    /// normally do, i.e. calling [fmt::Display] on provided [Report]s.
    #[default]
    Normal,
}

impl fmt::Display for CompilerMessagingFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CompilerMessagingFormat::Json => write!(f, "json"),
            CompilerMessagingFormat::Normal => write!(f, "normal"),
        }
    }
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
    messaging_format: OnceCell<CompilerMessagingFormat>,
}

impl CompilerLogger {
    /// Create a new compiler logger.
    pub const fn new() -> Self {
        Self {
            output_stream: OnceCell::new(),
            error_stream: OnceCell::new(),
            messaging_format: OnceCell::new(),
        }
    }

    /// Set the [CompilerLogger] messaging format.
    pub fn set_messaging_format(&self, format: CompilerMessagingFormat) {
        self.messaging_format.set(format).unwrap();
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

        if *self.messaging_format.get().unwrap() == CompilerMessagingFormat::Json {
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
