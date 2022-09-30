//! Hash Compiler entry point.
#![feature(panic_info_message)]

mod args;
mod crash_handler;
mod logger;

use std::{num::NonZeroUsize, panic};

use clap::Parser as ClapParser;
use hash_ast_desugaring::AstDesugaringPass;
use hash_ast_expand::AstExpansionPass;
use hash_lower::IrLowerer;
use hash_parser::Parser;
use hash_pipeline::{settings::CompilerSettings, traits::CompilerStage, Compiler};
use hash_reporting::errors::CompilerError;
use hash_source::ModuleKind;
use hash_typecheck::Typechecker;
use hash_untyped_semantics::SemanticAnalysis;
use hash_vm::vm::Interpreter;
use log::LevelFilter;
use logger::CompilerLogger;

use crate::{
    args::{AstGenMode, CheckMode, CompilerOptions, DeSugarMode, IrGenMode, SubCmd},
    crash_handler::panic_handler,
};

pub static CONSOLE_LOGGER: CompilerLogger = CompilerLogger;

fn execute(f: impl FnOnce() -> Result<(), CompilerError>) {
    match f() {
        Ok(()) => (),
        Err(e) => e.report_and_exit(),
    }
}

fn main() {
    // Initial grunt work, panic handler and logger setup...
    panic::set_hook(Box::new(panic_handler));
    log::set_logger(&CONSOLE_LOGGER).unwrap_or_else(|_| panic!("Couldn't initiate logger"));

    // Starting the Tracy client is necessary before any invoking any of its APIs
    #[cfg(feature = "profile-with-tracy")]
    tracy_client::Client::start();

    // Register main thread with the profiler
    profiling::register_thread!("Main Thread");

    let opts: CompilerOptions = CompilerOptions::parse();

    // if debug is specified, we want to log everything that is debug level...
    if opts.debug {
        log::set_max_level(LevelFilter::Debug);
    } else {
        log::set_max_level(LevelFilter::Info);
    }

    // We want to figure out the entry point of the compiler by checking if the
    // compiler has been specified to run in a specific mode.
    let entry_point = match &opts.mode {
        Some(SubCmd::AstGen(AstGenMode { filename })) => Some(filename.clone()),
        Some(SubCmd::DeSugar(DeSugarMode { filename })) => Some(filename.clone()),
        Some(SubCmd::IrGen(IrGenMode { filename })) => Some(filename.clone()),
        Some(SubCmd::Check(CheckMode { filename })) => Some(filename.clone()),
        None => opts.filename.clone(),
    };

    // check that the job count is valid...
    let worker_count: usize = NonZeroUsize::new(opts.worker_count)
        .unwrap_or_else(|| {
            (CompilerError::ArgumentError {
                message: "Invalid number of worker threads".to_owned(),
            })
            .report_and_exit()
        })
        .into();

    // We need at least 2 workers for the parsing loop in order so that the job
    // queue can run within a worker and any other jobs can run inside another
    // worker or workers.
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(worker_count + 1)
        .thread_name(|id| format!("compiler-worker-{}", id))
        .build()
        .unwrap();

    let compiler_settings: CompilerSettings = opts.into();
    let compiler_stages: Vec<Box<dyn CompilerStage>> = vec![
        Box::new(Parser::new()),
        Box::new(AstExpansionPass),
        Box::new(AstDesugaringPass),
        Box::new(SemanticAnalysis),
        Box::new(Typechecker::new()),
        Box::new(IrLowerer::new()),
        Box::new(Interpreter::new()),
    ];

    let mut compiler = Compiler::new(compiler_stages, pool, compiler_settings);
    let compiler_state = compiler.bootstrap();

    match entry_point {
        Some(path) => {
            execute(|| {
                compiler.run_on_filename(path, ModuleKind::Normal, compiler_state);
                Ok(())
            });
        }
        None => {
            execute(|| {
                hash_interactive::init(compiler, compiler_state)?;
                Ok(())
            });
        }
    };
}
