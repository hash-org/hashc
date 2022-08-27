//! Hash Compiler pipeline implementation. The pipeline is a abstract
//! representation of the compiler flow managing the compiling steps like
//! parsing, typechecking, optimisation passes, etc. The pipeline is used to
//! abstract away the idea of depending on specific implementations of the
//! parser or typechecker and just use a common trait interface that can be
//! used. This file also has definitions for how to access sources whether
//! module or interactive.
#![allow(clippy::too_many_arguments)]

pub mod fs;
pub mod settings;
pub mod sources;
pub mod traits;

use std::{collections::HashMap, env, time::Duration};

use fs::{read_in_path, resolve_path, PRELUDE};
use hash_ast::{ast::OwnsAstNode, tree::AstTreeGenerator, visitor::AstVisitor};
use hash_reporting::{report::Report, writer::ReportWriter};
use hash_source::{ModuleKind, SourceId};
use hash_utils::{path::adjust_canonicalisation, timing::timed, tree_writing::TreeWriter};
use settings::{CompilerJobParams, CompilerMode, CompilerSettings};
use sources::{Module, Workspace};
use traits::{Desugar, Lowering, Parser, SemanticPass, Tc, VirtualMachine};

pub type CompilerResult<T> = Result<T, Vec<Report>>;

/// The Hash Compiler interface. This interface allows a caller to create a
/// [Compiler] with the specified components. This allows external tinkerers
/// to add their own implementations of each compiler stage with relative ease
/// instead of having to scratch their heads.
pub struct Compiler<'pool, P, D, S, C, L, V> {
    /// The parser stage of the compiler.
    parser: P,
    /// De-sugar the AST
    desugarer: D,
    /// Perform semantic analysis on the AST.
    semantic_analyser: S,
    /// The typechecking stage of the compiler.
    checker: C,
    /// The IR Lowerer.
    lowerer: L,
    /// The current VM.
    vm: V,
    /// Various settings for the compiler.
    pub settings: CompilerSettings,
    /// The pipeline shared thread pool.
    pool: &'pool rayon::ThreadPool,

    /// A record of all of the stage metrics
    metrics: HashMap<CompilerMode, Duration>,
}

/// The [CompilerState] holds all the information and state of the compiler
/// instance. Each stage of the compiler contains a `State` type parameter which
/// the compiler stores so that incremental executions of the compiler are
/// possible.
pub struct CompilerState<
    'c,
    'pool,
    D: Desugar<'pool>,
    S: SemanticPass<'pool>,
    C: Tc<'c>,
    L: Lowering<'c>,
    V: VirtualMachine<'c>,
> {
    /// The collected workspace sources for the current job.
    pub workspace: Workspace,
    /// Any diagnostics that were collected from any stage
    pub diagnostics: Vec<Report>,
    /// The typechecker state.
    pub ds_state: D::State,
    /// The semantic analysis state.
    pub semantic_analysis_state: S::State,
    /// The typechecker state.
    pub tc_state: C::State,
    /// The IR Lowering state.
    pub lowering_state: L::State,
    /// The State of the Virtual machine
    pub vm_state: V::State,
}

impl<'c, 'pool, P, D, S, C, L, V> Compiler<'pool, P, D, S, C, L, V>
where
    'pool: 'c,
    P: Parser<'pool>,
    D: Desugar<'pool>,
    S: SemanticPass<'pool>,
    C: Tc<'c>,
    L: Lowering<'c>,
    V: VirtualMachine<'c>,
{
    /// Create a new instance of a [Compiler] with the provided parser and
    /// typechecker implementations.
    pub fn new(
        parser: P,
        desugarer: D,
        semantic_analyser: S,
        checker: C,
        lowerer: L,
        vm: V,
        pool: &'pool rayon::ThreadPool,
        settings: CompilerSettings,
    ) -> Self {
        Self {
            parser,
            desugarer,
            semantic_analyser,
            checker,
            lowerer,
            vm,
            settings,
            pool,
            metrics: HashMap::new(),
        }
    }

    /// Create a compiler state to accompany with compiler execution.
    /// Internally, this calls the [Tc] state making functions and saves it
    /// into the created [CompilerState].
    pub fn create_state(&mut self) -> CompilerResult<CompilerState<'c, 'pool, D, S, C, L, V>> {
        let workspace = Workspace::new();

        let desugaring_state = self.desugarer.make_state()?;
        let semantic_analysis_state = self.semantic_analyser.make_state()?;
        let tc_state = self.checker.make_state()?;
        let lowering_state = self.lowerer.make_state()?;
        let vm_state = self.vm.make_state()?;

        Ok(CompilerState {
            workspace,
            diagnostics: vec![],
            ds_state: desugaring_state,
            semantic_analysis_state,
            tc_state,
            lowering_state,
            vm_state,
        })
    }

    /// Function to report the collected metrics on the stages within the
    /// compiler.
    fn report_metrics(&self) {
        let mut total = Duration::new(0, 0);

        // Sort metrics by the declared order
        let mut timings: Vec<_> = self.metrics.iter().collect();
        timings.sort_by_key(|entry| entry.0);

        log::debug!("compiler pipeline timings:");

        for (stage, duration) in timings {
            // This shouldn't occur as we don't record this metric in this way
            if *stage == CompilerMode::Full {
                continue;
            }
            total += *duration;

            eprintln!("{: <12}: {duration:?}", format!("{}", stage));
        }

        // Now print the total
        eprintln!("{: <12}: {total:?}\n", format!("{}", CompilerMode::Full));
    }

    /// Utility function used by AST-like stages in order to print the
    /// current [self::sources::NodeMap].
    fn print_sources(&self, workspace: &Workspace, entry_point: SourceId) {
        match entry_point {
            SourceId::Interactive(id) => {
                // If this is an interactive statement, we want to print the statement that was
                // just parsed.
                let source = workspace.node_map().get_interactive_block(id);
                let tree = AstTreeGenerator.visit_body_block(&(), source.node_ref()).unwrap();

                println!("{}", TreeWriter::new(&tree));
            }
            SourceId::Module(_) => {
                // If this is a module, we want to print all of the generated modules from the
                // parsing stage
                for (_, generated_module) in workspace.node_map().iter_modules() {
                    let tree =
                        AstTreeGenerator.visit_module(&(), generated_module.node_ref()).unwrap();

                    println!(
                        "Tree for `{}`:\n{}",
                        adjust_canonicalisation(generated_module.path()),
                        TreeWriter::new(&tree)
                    );
                }
            }
        }
    }

    /// Function to invoke a parsing job of a specified [SourceId].
    fn parse_source(
        &mut self,
        entry_point: SourceId,
        workspace: &mut Workspace,
        job_params: &CompilerJobParams,
    ) -> CompilerResult<()> {
        timed(
            || self.parser.parse(entry_point, workspace, self.pool),
            log::Level::Debug,
            |time| {
                self.metrics.insert(CompilerMode::Parse, time);
            },
        )?;

        // We want to loop through all of the generated modules and print
        // the resultant AST
        if job_params.mode == CompilerMode::Parse && job_params.output_stage_result {
            self.print_sources(workspace, entry_point);
        }

        Ok(())
    }

    /// De-sugaring stage within the pipeline.
    fn desugar_sources(
        &mut self,
        entry_point: SourceId,
        workspace: &mut Workspace,
        desugar_state: &mut D::State,
        job_params: &CompilerJobParams,
    ) -> CompilerResult<()> {
        timed(
            || self.desugarer.desugar(entry_point, workspace, desugar_state, self.pool),
            log::Level::Debug,
            |time| {
                self.metrics.insert(CompilerMode::DeSugar, time);
            },
        )?;

        // We want to loop through all of the generated modules and print
        // the resultant AST
        if job_params.mode == CompilerMode::DeSugar && job_params.output_stage_result {
            self.print_sources(workspace, entry_point);
        }

        Ok(())
    }

    /// Semantic pass stage within the pipeline.
    fn check_source_semantics(
        &mut self,
        entry_point: SourceId,
        workspace: &mut Workspace,
        semantic_analyser_state: &mut S::State,
        _job_params: &CompilerJobParams,
    ) -> Result<(), Vec<Report>> {
        timed(
            || {
                self.semantic_analyser.perform_pass(
                    entry_point,
                    workspace,
                    semantic_analyser_state,
                    self.pool,
                )
            },
            log::Level::Debug,
            |time| {
                self.metrics.insert(CompilerMode::SemanticPass, time);
            },
        )?;

        Ok(())
    }

    /// Function to invoke the typechecking stage for the entry point denoted by
    /// the passed [SourceId].
    ///
    /// This function also expects the [CompilerSettings] for the current pass
    /// in order to determine if it should output the result from the
    /// operation. This is only relevant when the [SourceId] is interactive
    /// as it might be specified that the pipeline output the type of the
    /// current expression. This directly comes from a user using the `:t`
    /// mode in the REPL as so:
    ///
    /// ```text
    /// >>> :t foo(3);
    /// ```
    fn typecheck_sources(
        &mut self,
        entry_point: SourceId,
        workspace: &mut Workspace,
        checker_state: &mut C::State,
        job_params: &CompilerJobParams,
    ) -> CompilerResult<()> {
        match entry_point {
            SourceId::Interactive(id) => {
                timed(
                    || self.checker.check_interactive(id, workspace, checker_state, job_params),
                    log::Level::Debug,
                    |time| {
                        self.metrics.insert(CompilerMode::Typecheck, time);
                    },
                )?;
            }
            SourceId::Module(id) => {
                timed(
                    || self.checker.check_module(id, workspace, checker_state, job_params),
                    log::Level::Debug,
                    |time| {
                        self.metrics.insert(CompilerMode::Typecheck, time);
                    },
                )?;
            }
        };

        Ok(())
    }

    /// Function to invoke the IR Lowering stage for the entry point denoted by
    /// the passed [SourceId].
    fn lower_sources(
        &mut self,
        entry_point: SourceId,
        workspace: &mut Workspace,
        lowering_state: &mut L::State,
        job_params: &CompilerJobParams,
    ) -> CompilerResult<()> {
        match entry_point {
            SourceId::Interactive(id) => {
                timed(
                    || {
                        self.lowerer.lower_interactive_block(
                            id,
                            workspace,
                            lowering_state,
                            job_params,
                        )
                    },
                    log::Level::Debug,
                    |time| {
                        self.metrics.insert(CompilerMode::IrGen, time);
                    },
                )?;
            }
            SourceId::Module(id) => {
                timed(
                    || self.lowerer.lower_module(id, workspace, lowering_state, job_params),
                    log::Level::Debug,
                    |time| {
                        self.metrics.insert(CompilerMode::IrGen, time);
                    },
                )?;
            }
        };

        Ok(())
    }

    /// Helper function in order to check if the pipeline needs to terminate
    /// after any stage on the condition that the [CompilerJobParams]
    /// specify that this is the last stage, or if the previous stage had
    /// generated any errors that are fatal and an abort is necessary.
    fn maybe_terminate(
        &self,
        result: CompilerResult<()>,
        compiler_state: &mut CompilerState<'c, 'pool, D, S, C, L, V>,
        job_params: &CompilerJobParams,
        // @@TODO(feds01): remove this parameter, it would be ideal that this parameter is stored
        // within the compiler state
        current_stage: CompilerMode,
    ) -> Result<(), ()> {
        if let Err(diagnostics) = result {
            compiler_state.diagnostics.extend(diagnostics.into_iter());

            // Some diagnostics might not be errors and all just warnings, in this
            // situation, we don't have to terminate execution
            if compiler_state.diagnostics.iter().any(|r| r.is_error()) {
                return Err(());
            }
        }

        // Terminate the pipeline if we have reached the stage regardless of error state
        if job_params.mode == current_stage {
            return Err(());
        }

        Ok(())
    }

    /// Run a particular job within the pipeline. The function deals with
    /// executing the required stages in order as specified by the
    /// `job_parameters`
    fn run_pipeline(
        &mut self,
        entry_point: SourceId,
        compiler_state: &mut CompilerState<'c, 'pool, D, S, C, L, V>,
        job_params: CompilerJobParams,
    ) -> Result<(), ()> {
        let result = self.parse_source(entry_point, &mut compiler_state.workspace, &job_params);
        self.maybe_terminate(result, compiler_state, &job_params, CompilerMode::Parse)?;

        let result = self.desugar_sources(
            entry_point,
            &mut compiler_state.workspace,
            &mut compiler_state.ds_state,
            &job_params,
        );
        self.maybe_terminate(result, compiler_state, &job_params, CompilerMode::DeSugar)?;

        // Now perform the semantic pass on the sources
        let result = self.check_source_semantics(
            entry_point,
            &mut compiler_state.workspace,
            &mut compiler_state.semantic_analysis_state,
            &job_params,
        );
        self.maybe_terminate(result, compiler_state, &job_params, CompilerMode::SemanticPass)?;

        let result = self.typecheck_sources(
            entry_point,
            &mut compiler_state.workspace,
            &mut compiler_state.tc_state,
            &job_params,
        );
        self.maybe_terminate(result, compiler_state, &job_params, CompilerMode::Typecheck)?;

        let result = self.lower_sources(
            entry_point,
            &mut compiler_state.workspace,
            &mut compiler_state.lowering_state,
            &job_params,
        );
        self.maybe_terminate(result, compiler_state, &job_params, CompilerMode::IrGen)?;

        Ok(())
    }

    /// Function to bootstrap the pipeline. This function invokes a job within
    /// the pipeline in order to load the prelude before any modules run.
    pub fn bootstrap(&mut self) -> CompilerState<'c, 'pool, D, S, C, L, V> {
        let mut compiler_state = self.create_state().unwrap();

        if !self.settings.skip_prelude {
            // we need to load in the `prelude` module and have it ready for any other
            // sources
            compiler_state = self.run_on_filename(
                PRELUDE.to_string(),
                ModuleKind::Prelude,
                compiler_state,
                CompilerJobParams::default(),
            );

            // The prelude shouldn't generate any errors, otherwise we just failed to
            // bootstrap
            if compiler_state.diagnostics.iter().any(|r| r.is_error()) {
                panic!("Failed to bootstrap compiler");
            }
        }

        compiler_state
    }

    /// Run a job within the compiler pipeline with the provided state, entry
    /// point and the specified job parameters.
    pub fn run(
        &mut self,
        entry_point: SourceId,
        mut compiler_state: CompilerState<'c, 'pool, D, S, C, L, V>,
        job_params: CompilerJobParams,
    ) -> CompilerState<'c, 'pool, D, S, C, L, V> {
        let result = self.run_pipeline(entry_point, &mut compiler_state, job_params);

        // we can print the diagnostics here
        if self.settings.emit_errors && (!compiler_state.diagnostics.is_empty() || result.is_err())
        {
            let mut err_count = 0;
            let mut warn_count = 0;

            // @@Copying: Ideally, we would not want to copy here!
            for diagnostic in compiler_state.diagnostics.clone().into_iter() {
                if diagnostic.is_error() {
                    err_count += 1;
                }

                if diagnostic.is_warning() {
                    warn_count += 1;
                }

                eprintln!(
                    "{}",
                    ReportWriter::new(diagnostic, compiler_state.workspace.source_map())
                );
            }

            // @@Hack: to prevent the compiler from printing this message when the pipeline
            // when it was instructed to terminate before all of the stages. For example, if
            // the compiler is just checking the source, then it will terminate early.
            if err_count != 0 || warn_count != 0 {
                log::info!(
                    "compiler terminated with {err_count} error(s), and {warn_count} warning(s)."
                );
            }
        }

        // Print compiler stage metrics if specified in the settings.
        if self.settings.display_metrics {
            self.report_metrics();
        }

        compiler_state
    }

    /// Run the compiler pipeline on a file specified by the path on the disk.
    /// This essentially performs the required steps of loading in a module
    /// off the disk, store it within the [Workspace] and invoke
    /// [`Self::run`]
    pub fn run_on_filename(
        &mut self,
        filename: impl Into<String>,
        kind: ModuleKind,
        mut compiler_state: CompilerState<'c, 'pool, D, S, C, L, V>,
        job_params: CompilerJobParams,
    ) -> CompilerState<'c, 'pool, D, S, C, L, V> {
        // First we have to work out if we need to transform the path
        let current_dir = env::current_dir().unwrap();
        let filename = resolve_path(filename.into(), current_dir, None);

        if let Err(err) = filename {
            compiler_state.diagnostics.push(err.create_report());

            // Only print the error if specified within the settings
            if self.settings.emit_errors {
                eprintln!(
                    "{}",
                    ReportWriter::new(err.create_report(), compiler_state.workspace.source_map())
                );
            }

            return compiler_state;
        };

        let filename = filename.unwrap();
        let contents = read_in_path(&filename);

        if let Err(err) = contents {
            compiler_state.diagnostics.push(err.create_report());

            // Only print the error if specified within the settings
            if self.settings.emit_errors {
                eprintln!(
                    "{}",
                    ReportWriter::new(err.create_report(), compiler_state.workspace.source_map())
                );
            }

            return compiler_state;
        };

        // Create the entry point and run!
        let entry_point =
            compiler_state.workspace.add_module(contents.unwrap(), Module::new(filename), kind);

        self.run(SourceId::Module(entry_point), compiler_state, job_params)
    }
}
