//! Main module.
//
// All rights reserved 2022 (c) The Hash Language authors

#![feature(panic_info_message)]

mod crash_handler;
mod logger;

use clap::Parser as ClapParser;
use hash_alloc::Castle;
use hash_ast::{tree::AstTreeGenerator, visitor::AstVisitor};
use hash_parser::parser::HashParser;
use hash_pipeline::{
    fs::resolve_path, settings::CompilerMode, settings::CompilerSettings, sources::Module, Compiler,
};
use hash_reporting::{errors::CompilerError, reporting::ReportWriter};
use hash_typecheck::HashTypechecker;
use hash_utils::{path::adjust_canonicalization, timed, tree_writing::TreeWriter};
use hash_vm::vm::{Interpreter, InterpreterOptions};
use log::LevelFilter;
use logger::CompilerLogger;
use std::num::NonZeroUsize;
use std::panic;
use std::{env, fs};

use crate::crash_handler::panic_handler;

/// CompilerOptions is a structural representation of what arguments the compiler
/// can take when running. Compiler options are well documented on the wiki page:
/// <https://hash-org.github.io/hash-arxiv/interpreter-options.html>
#[derive(ClapParser)]
#[clap(
    name = "Hash Interpreter",
    version,
    author = "Hash Language Authors",
    about = "Run and execute hash programs"
)]
#[clap(disable_colored_help = true)]
struct CompilerOptions {
    /// Execute the passed script directly without launching interactive mode
    #[clap(short, long)]
    filename: Option<String>,

    /// Run the compiler in debug mode
    #[clap(short, long)]
    debug: bool,

    /// Set the maximum stack size for the current running instance.
    #[clap(short, long, default_value = "10000")]
    stack_size: usize,

    /// Number of worker threads the compiler should use
    #[clap(short, long, default_value = Box::leak(num_cpus::get().to_string().into_boxed_str()))]
    worker_count: usize,

    /// Compiler mode
    #[clap(subcommand)]
    mode: Option<SubCmd>,
}

#[derive(ClapParser)]
enum SubCmd {
    AstGen(AstGen),
    IrGen(IrGen),
}

/// Generate AST from given input file
#[derive(ClapParser)]
struct AstGen {
    /// Input file to generate AST from
    #[clap(required = true)]
    filename: String,
}
/// Generate IR from the given input file
#[derive(ClapParser)]
struct IrGen {
    /// Input file to generate IR from
    #[clap(required = true)]
    filename: String,
}

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
        Some(SubCmd::AstGen(AstGen { filename })) => Some(filename.clone()),
        Some(SubCmd::IrGen(IrGen { filename })) => Some(filename.clone()),
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

    // Create a castle for allocations in the pipeline
    let castle = Castle::new();

    let parser = HashParser::new(worker_count, &castle);
    let tc_wall = &castle.wall();
    let checker = HashTypechecker::new(tc_wall);

    // Create the vm
    let vm = Interpreter::new(InterpreterOptions::new(opts.stack_size));

    let compiler_settings = match opts.mode {
        // @@Incomplete: We also want to integrate IrGen when we begin working on this
        Some(SubCmd::AstGen { .. }) => CompilerSettings::new(CompilerMode::AstGen),
        _ => CompilerSettings::default(),
    };

    let mut compiler = Compiler::new(parser, checker, vm, compiler_settings);
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
                let module_id = compiler_state.sources.add_module(module);

                // Wrap the compilation job in timed to time the total time taken to run the job
                let compiler_result = timed(
                    || {
                        let (result, new_state) = compiler.run_module(module_id, compiler_state);

                        // Report the error if one occurred...
                        if let Err(err) = result {
                            println!("{}", ReportWriter::new(err, &new_state.sources));

                            Err(())
                        } else {
                            Ok(new_state)
                        }
                    },
                    log::Level::Debug,
                    |elapsed| println!("total: {:?}", elapsed),
                );

                // @@Organisation: This should be moved out of this file into a potential 'modes' structure
                //                 so that we can differentiate between different modes and have a sane
                //                 structure when performing these kind of operations. We could also
                //                 look into using some kind of 'hook' system that u can register into the
                //                 pipeline when this runs instead of performing this operation here.

                // If the mode is ast-gen, and the `--debug` flag is specified, then we should
                // output the generated AST tree for the compiler
                if let Ok(new_state) = compiler_result {
                    if matches!(compiler_settings.mode, CompilerMode::AstGen) && opts.debug {
                        // We want to loop through all of the generated modules and print
                        // the resultant AST
                        for (_, generated_module) in new_state.sources.iter_modules() {
                            let tree = AstTreeGenerator
                                .visit_module(&(), generated_module.node())
                                .unwrap();

                            println!(
                                "Tree for `{}`:\n{}",
                                adjust_canonicalization(generated_module.path()),
                                TreeWriter::new(&tree)
                            );
                        }
                    }
                }

                Ok(())
            }
            None => {
                hash_interactive::init(compiler)?;
                Ok(())
            }
        }
    })
}
