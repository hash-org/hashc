//! Hash Compiler pipeline implementation. The pipeline is a abstract representation
//! of the compiler flow managing the compiling steps like parsing, typechecking, optimisation
//! passes, etc. The pipeline is used to abstract away the idea of depending on specific
//! implementations of the parser or typechecker and just use a common trait
//! interface that can be used. This file also has definitions for how to access
//! sources whether module or interactive.
//!
//! All rights reserved 2022 (c) The Hash Language authors

pub mod fs;
pub mod settings;
pub mod sources;
pub mod traits;

use std::{collections::HashMap, time::Duration};

use hash_ast::{tree::AstTreeGenerator, visitor::AstVisitor};
use hash_reporting::reporting::{Report, ReportWriter};
use hash_source::SourceId;
use hash_utils::{path::adjust_canonicalization, timed, tree_writing::TreeWriter};
use settings::{CompilerJobParams, CompilerMode, CompilerSettings};
use sources::Sources;
use traits::{Parser, Tc, VirtualMachine};

pub type CompilerResult<T> = Result<T, Report>;

/// The Hash Compiler interface. This interface allows a caller to create a
/// [Compiler] with the specified components. This allows external tinkerers
/// to add their own implementations of each compiler stage with relative ease
/// instead of having to scratch their heads.
pub struct Compiler<'pool, P, C, V> {
    /// The parser stage of the compiler.
    parser: P,
    /// The typechecking stage of the compiler.
    checker: C,
    /// The current VM.
    vm: V,
    /// Various settings for the compiler.
    pub settings: CompilerSettings,
    /// The pipeline shared thread pool.
    pool: &'pool rayon::ThreadPool,

    /// A record of all of the stage metrics
    metrics: HashMap<CompilerMode, Duration>,
}

/// The [CompilerState] holds all the information and state of the compiler instance.
/// Each stage of the compiler contains a `State` type parameter which the compiler stores
/// so that incremental executions of the compiler are possible.
pub struct CompilerState<'c, C: Tc<'c>, V: VirtualMachine<'c>> {
    /// The collected workspace sources for the current job.
    pub sources: Sources,
    /// Any errors that were collected from any stage
    _errors: Vec<Report>,
    /// The typechecker state.
    pub tc_state: C::State,
    /// The State of the Virtual machine
    pub vm_state: V::State,
}

impl<'c, 'pool, P, C, V> Compiler<'pool, P, C, V>
where
    'pool: 'c,
    P: Parser<'pool>,
    C: Tc<'c>,
    V: VirtualMachine<'c>,
{
    /// Create a new instance of a [Compiler] with the provided parser and
    /// typechecker implementations.
    pub fn new(
        parser: P,
        checker: C,
        vm: V,
        pool: &'pool rayon::ThreadPool,
        settings: CompilerSettings,
    ) -> Self {
        Self {
            parser,
            /// ast-desugaring
            /// semantic-analysis
            checker,
            /// monomorphisation
            /// lowering
            /// ir
            /// bytecode generation
            vm,
            settings,
            pool,
            metrics: HashMap::new(),
        }
    }

    /// Create a compiler state to accompany with compiler execution. Internally, this
    /// calls the [Tc] state making functions and saves it into the created
    /// [CompilerState].
    pub fn create_state(&mut self) -> CompilerResult<CompilerState<'c, C, V>> {
        let sources = Sources::new();
        // let checker_interactive_state = self.checker.make_interactive_state(&mut checker_state)?;
        // let checker_module_state = self.checker.make_module_state(&mut checker_state)?;

        let tc_state = self.checker.make_state()?;
        let vm_state = self.vm.make_state()?;

        Ok(CompilerState {
            sources,
            _errors: vec![],
            tc_state,
            vm_state,
        })
    }

    /// Function to report the collected metrics on the stages within the compiler.
    fn report_metrics(&self) {
        let mut total = Duration::new(0, 0);

        // Sort metrics by the declared order
        let mut timings: Vec<_> = self.metrics.iter().collect();
        timings.sort_by_key(|entry| entry.0);

        for (stage, duration) in timings {
            // This shouldn't occur as we don't record this metric in this way
            if *stage == CompilerMode::Full {
                continue;
            }
            total += *duration;

            println!("{: <9}: {duration:?}", format!("{}", stage));
        }

        // Now print the total
        println!("{: <9}: {total:?}", format!("{}", CompilerMode::Full));
    }

    /// Function to print a returned error from any stage in the pipeline. This function
    /// also deals with printing metrics if it is specified within the [CompilerSettings].
    ///
    /// @@TODO: we want to essentially integrate this with the stages in order to
    /// collect errors rather than immediately printing them
    fn report_error(&self, error: Report, sources: &Sources) {
        if self.settings.display_metrics {
            self.report_metrics();
        }

        println!("{}", ReportWriter::new(error, sources));
    }

    /// Function to invoke a parsing job of a specified [SourceId].
    fn parse_source(
        &mut self,
        entry_point: SourceId,
        sources: &mut Sources,
        job_params: &CompilerJobParams,
    ) -> CompilerResult<()> {
        timed(
            || self.parser.parse(entry_point, sources, self.pool),
            log::Level::Debug,
            |time| {
                self.metrics.insert(CompilerMode::Parse, time);
            },
        )?;

        // We want to loop through all of the generated modules and print
        // the resultant AST
        if job_params.mode == CompilerMode::Parse && job_params.output_stage_result {
            match entry_point {
                SourceId::Interactive(id) => {
                    // If this is an interactive statement, we want to print the statement that was just parsed.
                    let source = sources.get_interactive_block(id);

                    let tree = AstTreeGenerator
                        .visit_body_block(&(), source.node())
                        .unwrap();

                    println!("{}", TreeWriter::new(&tree));
                }
                SourceId::Module(_) => {
                    // If this is a module, we want to print all of the generated modules from the parsing stage
                    for (_, generated_module) in sources.iter_modules() {
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
        }

        Ok(())
    }

    /// Function to invoke the typechecking stage for the entry point denoted by
    /// the passed [SourceId].
    ///
    /// This function also expects the [CompilerSettings] for the current pass in order
    /// to determine if it should output the result from the operation. This is only
    /// relevant when the [SourceId] is interactive as it might be specified that the
    /// pipeline output the type of the current expression. This directly comes from
    /// a user using the `:t` mode in the REPL as so:
    ///
    /// ```text
    /// >>> :t foo(3);
    /// ```
    fn typecheck_source(
        &mut self,
        entry_point: SourceId,
        sources: &mut Sources,
        checker_state: &mut C::State,
        job_params: &CompilerJobParams,
    ) -> CompilerResult<()> {
        match entry_point {
            SourceId::Interactive(id) => {
                let result = timed(
                    || self.checker.check_interactive(id, sources, checker_state),
                    log::Level::Debug,
                    |time| {
                        self.metrics.insert(CompilerMode::Typecheck, time);
                    },
                )?;

                // So here, we print the result of the type that was inferred from the passed statement
                if job_params.mode == CompilerMode::Typecheck && job_params.output_stage_result {
                    println!("= {result}")
                }
            }
            SourceId::Module(id) => {
                timed(
                    || self.checker.check_module(id, sources, checker_state),
                    log::Level::Debug,
                    |time| {
                        self.metrics.insert(CompilerMode::Typecheck, time);
                    },
                )?;
            }
        };

        Ok(())
    }

    /// Run a particular job within the pipeline. This function handles both cases of either the
    /// entry point being an [InteractiveId] or a [ModuleId]. The function deals with executing the
    /// required stages in order as specified by the `job_parameters`
    pub fn run(
        &mut self,
        entry_point: SourceId,
        mut compiler_state: CompilerState<'c, C, V>,
        job_params: CompilerJobParams,
    ) -> CompilerState<'c, C, V> {
        let parse_result = self.parse_source(entry_point, &mut compiler_state.sources, &job_params);

        // Short circuit if parsing failed or the job specified to stop at parsing
        if parse_result.is_err() || job_params.mode == CompilerMode::Parse {
            if let Err(err) = parse_result {
                self.report_error(err, &compiler_state.sources);
            }

            return compiler_state;
        }

        let tc_result = self.typecheck_source(
            entry_point,
            &mut compiler_state.sources,
            &mut compiler_state.tc_state,
            &job_params,
        );

        // Short circuit if tc failed or the job specified to stop at tc
        if tc_result.is_err() || job_params.mode == CompilerMode::Typecheck {
            if let Err(err) = tc_result {
                self.report_error(err, &compiler_state.sources);
            }

            return compiler_state;
        }

        // Print compiler stage metrics if specified in the settings.
        if self.settings.display_metrics {
            self.report_metrics();
        }

        compiler_state
    }
}
