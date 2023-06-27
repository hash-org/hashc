//! Hash Compiler entry point.
#![feature(panic_info_message)]

mod crash_handler;
mod logger;

use std::{
    panic,
    process::{Command, Stdio},
};

use clap::Parser;
use hash_pipeline::{
    interface::CompilerInterface,
    settings::{CompilerSettings, CompilerStageKind},
};
use hash_session::CompilerBuilder;
use hash_utils::log;
use log::LevelFilter;
use logger::CompilerLogger;

use crate::crash_handler::panic_handler;

/// The logger that is used by the compiler for `log!` statements.
pub static COMPILER_LOGGER: CompilerLogger = CompilerLogger;

fn main() {
    // Initial grunt work, panic handler and logger setup...
    panic::set_hook(Box::new(panic_handler));
    log::set_logger(&COMPILER_LOGGER).unwrap_or_else(|_| panic!("couldn't initiate logger"));

    // Starting the Tracy client is necessary before any invoking any of its APIs
    #[cfg(feature = "profile-with-tracy")]
    tracy_client::Client::start();

    // Register main thread with the profiler
    profiling::register_thread!("compiler-main");

    let settings = CompilerSettings::parse();

    // if debug is specified, we want to log everything that is debug level...
    if settings.debug {
        log::set_max_level(LevelFilter::Debug);
    } else {
        log::set_max_level(LevelFilter::Info);
    }

    let mut compiler = CompilerBuilder::build_with_settings(settings);

    // Now run on the filename that was specified by the user.
    compiler.run_on_entry_point();

    let session = compiler.session();
    // If the stage is set to `exe`, this means that we want to run the
    // produced executable from the building process. This is essentially
    // a shorthand for `hash build <file> && ./<exe_path>`.
    let workspace = session.workspace();
    let settings = session.settings();

    if settings.stage == CompilerStageKind::Exe
        && workspace.yields_executable(settings)
        && !session.has_errors()
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
