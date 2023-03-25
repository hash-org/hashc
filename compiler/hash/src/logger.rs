//! Hash main crate logging utilities
use hash_reporting::highlight::{highlight, Colour, Modifier};
use hash_utils::{
    log::{Level, Log, Metadata, Record},
    stream_less_writeln,
};

pub struct CompilerLogger;

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

            // ##Streams: we don't stream this since this is always meant to be a debugging
            // message, thus it is never tested for anyway.
            stream_less_writeln!("{level_prefix}: {}", record.args());
        }
    }

    fn flush(&self) {}
}
