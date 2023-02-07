//! Hash Compiler entry point.
#![feature(panic_info_message)]

mod crash_handler;
mod logger;

use std::panic;

use hash_pipeline::{
    args::parse_settings_from_args, interface::CompilerOutputStream, settings::CompilerSettings,
    workspace::Workspace, Compiler,
};
use hash_reporting::report::Report;
use hash_session::{emit_fatal_error, make_stages, CompilerSession};
use hash_source::{ModuleKind, SourceMap};
use log::LevelFilter;
use logger::CompilerLogger;

use crate::crash_handler::panic_handler;

/// THe logger that is used by the compiler for `log!` statements.
pub static COMPILER_LOGGER: CompilerLogger = CompilerLogger;

/// Perform some task that might fail and if it does, report the error and exit,
/// otherwise return the result of the task.
fn execute<T, E: Into<Report>>(sources: &SourceMap, f: impl FnOnce() -> Result<T, E>) -> T {
    match f() {
        Ok(value) => value,
        Err(err) => emit_fatal_error(err, sources),
    }
}

fn main() {
    // Initial grunt work, panic handler and logger setup...
    panic::set_hook(Box::new(panic_handler));
    log::set_logger(&COMPILER_LOGGER).unwrap_or_else(|_| panic!("couldn't initiate logger"));

    // Starting the Tracy client is necessary before any invoking any of its APIs
    #[cfg(feature = "profile-with-tracy")]
    tracy_client::Client::start();

    // Register main thread with the profiler
    profiling::register_thread!("compiler-main");

    // @@Hack: we have to create a dummy source map here so that we can use it
    // to report errors in the case that the compiler fails to start up. After the
    // workspace is initiated, it is replaced with the real source map.
    let source_map = SourceMap::new();

    let settings: CompilerSettings = execute(&source_map, parse_settings_from_args);

    // We want to figure out the entry point of the compiler by checking if the
    // compiler has been specified to run in a specific mode.
    let entry_point = execute(&source_map, || settings.entry_point().transpose());
    let workspace = execute(&source_map, || Workspace::new(&settings));

    // if debug is specified, we want to log everything that is debug level...
    if settings.debug {
        log::set_max_level(LevelFilter::Debug);
    } else {
        log::set_max_level(LevelFilter::Info);
    }

    // We need at least 2 workers for the parsing loop in order so that the job
    // queue can run within a worker and any other jobs can run inside another
    // worker or workers.
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(settings.worker_count + 1)
        .thread_name(|id| format!("compiler-worker-{id}"))
        .build()
        .unwrap();

    let session = CompilerSession::new(
        workspace,
        pool,
        settings,
        || CompilerOutputStream::Stderr(std::io::stderr()),
        || CompilerOutputStream::Stdout(std::io::stdout()),
    );
    let mut compiler = Compiler::new(make_stages());
    let compiler_state = compiler.bootstrap(session);

    match entry_point {
        Some(path) => {
            compiler.run_on_filename(path, ModuleKind::EntryPoint, compiler_state);
        }
        None => {
            hash_interactive::init(compiler, compiler_state);
        }
    };
}
