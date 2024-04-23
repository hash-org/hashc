//! Hash Compiler entry point.
use std::panic;

use hash_driver::CompilerBuilder;
use hash_pipeline::settings::CompilerSettings;
use hash_utils::{crash::crash_handler, log, logging::CompilerLogger};

/// The logger that is used by the compiler for `log!` statements.
pub static COMPILER_LOGGER: CompilerLogger = CompilerLogger;

fn main() {
    // Initial grunt work, panic handler and logger setup...
    panic::set_hook(Box::new(crash_handler));
    log::set_logger(&COMPILER_LOGGER).unwrap_or_else(|_| panic!("couldn't initiate logger"));

    // Starting the Tracy client is necessary before any invoking any of its APIs
    #[cfg(feature = "profile-with-tracy")]
    tracy_client::Client::start();

    // Register main thread with the profiler
    profiling::register_thread!("compiler-main");

    let settings = CompilerSettings::new_from_args();

    // if debug is specified, we want to log everything that is debug level...
    if settings.debug {
        log::set_max_level(log::LevelFilter::Debug);
    } else {
        log::set_max_level(log::LevelFilter::Info);
    }

    let mut compiler = CompilerBuilder::build_with_settings(settings);

    // Now run on the filename that was specified by the user.
    compiler.run_on_entry_point();
    compiler.maybe_run_executable();
}
