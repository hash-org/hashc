//! Hash Compiler entry point.
use std::{
    panic,
    process::{Command, Stdio},
};

use hash_driver::CompilerBuilder;
use hash_pipeline::{
    interface::CompilerInterface,
    settings::{CompilerSettings, CompilerStageKind},
};
use hash_utils::{clap::Parser, crash::crash_handler, log, logging::CompilerLogger};

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

    let settings = CompilerSettings::parse();

    // if debug is specified, we want to log everything that is debug level...
    if settings.debug {
        log::set_max_level(log::LevelFilter::Debug);
    } else {
        log::set_max_level(log::LevelFilter::Info);
    }

    let mut compiler = CompilerBuilder::build_with_settings(settings);

    // Now run on the filename that was specified by the user.
    compiler.run_on_entry_point();

    // If the stage is set to `exe`, this means that we want to run the
    // produced executable from the building process. This is essentially
    // a shorthand for `hash build <file> && ./<exe_path>`.
    let workspace = compiler.workspace();
    let settings = compiler.settings();

    if settings.stage == CompilerStageKind::Exe
        && workspace.yields_executable(settings)
        && !compiler.has_errors()
    {
        let path = workspace.executable_path(settings);

        // We need to convert the path to a string so that we can pass it
        // to the `Command` struct.
        let path = path.to_str().unwrap();

        // @@Todo: ideally, we should be able to parse the arguments that are specified
        // after `--` into the spawned process.
        Command::new(path)
            .stdin(Stdio::inherit())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap()
            .wait()
            .unwrap();
    }
}
