//! Hash Compiler entry point.
//!
//! All rights reserved 2022 (c) The Hash Language authors

#![feature(panic_info_message)]

mod args;
mod crash_handler;
mod logger;

use clap::Parser as ClapParser;
use hash_ast_desugaring::AstDesugaring;
use hash_ast_passes::HashSemanticAnalysis;
use hash_parser::HashParser;
use hash_pipeline::{
    fs::resolve_path,
    settings::{CompilerJobParams, CompilerMode, CompilerSettings},
    sources::Module,
    Compiler,
};
use hash_reporting::{errors::CompilerError, reporting::ReportWriter};
use hash_source::SourceId;
use hash_typecheck::Typechecker;
use hash_vm::vm::{Interpreter, InterpreterOptions};
use log::LevelFilter;
use logger::CompilerLogger;
use std::num::NonZeroUsize;
use std::panic;
use std::{env, fs};

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
        None => opts.filename,
    };

    // check that the job count is valid...
    let worker_count = NonZeroUsize::new(opts.worker_count)
        .unwrap_or_else(|| {
            (CompilerError::ArgumentError {
                message: "Invalid number of worker threads".to_owned(),
            })
            .report_and_exit()
        })
        .into();

    // @@Naming: think about naming here!
    let parser = HashParser::new();
    let desugarer = AstDesugaring;
    let semnatic_analyser = HashSemanticAnalysis;
    let checker = Typechecker;

    // Create the vm
    let vm = Interpreter::new(InterpreterOptions::new(opts.stack_size));
    let compiler_settings = CompilerSettings::new(opts.debug, worker_count);

    // We need at least 2 workers for the parsing loop in order so that the job queue can run
    // within a worker and any other jobs can run inside another worker or workers.
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(worker_count + 1)
        .thread_name(|id| format!("compiler-worker-{}", id))
        .build()
        .unwrap();

    let mut compiler = Compiler::new(
        parser,
        desugarer,
        semnatic_analyser,
        checker,
        vm,
        &pool,
        compiler_settings,
    );
    let mut compiler_state = compiler.create_state().unwrap();

    execute(|| {
        match entry_point {
            Some(path) => {
                // First we have to work out if we need to transform the path
                let current_dir = env::current_dir()?;
                let filename = resolve_path(fs::canonicalize(&path)?, current_dir, None);

                if let Err(err) = filename {
                    println!(
                        "{}",
                        ReportWriter::new(err.create_report(), &compiler_state.sources)
                    );

                    return Ok(());
                };

                let module = Module::new(filename.unwrap());
                let entry_point = SourceId::Module(compiler_state.sources.add_module(module));

                let job_settings = match opts.mode {
                    Some(SubCmd::AstGen { .. }) => {
                        CompilerJobParams::new(CompilerMode::Parse, opts.debug)
                    }
                    Some(SubCmd::DeSugar { .. }) => {
                        CompilerJobParams::new(CompilerMode::DeSugar, opts.debug)
                    }
                    Some(SubCmd::Check { .. }) => {
                        CompilerJobParams::new(CompilerMode::Typecheck, opts.debug)
                    }
                    Some(SubCmd::IrGen { .. }) => {
                        CompilerJobParams::new(CompilerMode::IrGen, opts.debug)
                    }
                    _ => CompilerJobParams::default(),
                };

                compiler.run(entry_point, compiler_state, job_settings);
            }
            None => {
                hash_interactive::init(compiler)?;
            }
        };

        Ok(())
    })
}
