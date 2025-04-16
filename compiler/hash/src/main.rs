//! Hash Compiler entry point.
use std::panic;

use hash_driver::{CompilerBuilder, utils};
use hash_pipeline::settings::CompilerSettings;
use hash_utils::{
    crash::crash_handler, log, logging::CompilerLogger, stream::CompilerOutputStream,
};

/// The logger that is used by the compiler for `log!` statements.
pub static COMPILER_LOGGER: CompilerLogger = CompilerLogger::new();

fn main() {
    // Initial grunt work, panic handler and logger setup...
    panic::set_hook(Box::new(crash_handler));

    let output_stream = CompilerOutputStream::stdout;
    let error_stream = CompilerOutputStream::stderr;

    COMPILER_LOGGER.error_stream.set(error_stream()).unwrap();
    COMPILER_LOGGER.output_stream.set(output_stream()).unwrap();
    log::set_logger(&COMPILER_LOGGER).unwrap_or_else(|_| panic!("couldn't initiate logger"));

    // Starting the Tracy client is necessary before any invoking any of its APIs
    #[cfg(feature = "tracy")]
    tracy_client::Client::start();

    // Register main thread with the profiler
    profiling::register_thread!("compiler-main");

    let settings = utils::emit_on_fatal_error(error_stream(), CompilerSettings::from_cli);

    // @@TODO: find a neater way of setting this, as in what if initialising the
    // `settings` fails and we need to actually output in the `json` format
    // right from the start.
    COMPILER_LOGGER.set_messaging_format(settings.messaging_format);

    // if debug is specified, we want to log everything that is debug level...
    if settings.debug {
        log::set_max_level(log::LevelFilter::Debug);
    } else {
        log::set_max_level(log::LevelFilter::Info);
    }

    // if `emit_schema` is true, that's the only thing that we should do since this
    // is a schema generation request.
    if settings.emit_schema {
        utils::emit_schema_to(output_stream());
        return;
    }

    let mut compiler = CompilerBuilder::build_with_settings(settings, error_stream, output_stream);

    // Now run on the filename that was specified by the user.
    compiler.run_on_entry_point();
    compiler.maybe_run_executable();
}
