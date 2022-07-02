//! Hash Compiler pipeline implementation. The pipeline is a abstract
//! representation of the compiler flow managing the compiling steps like
//! parsing, typechecking, optimisation passes, etc. The pipeline is used to
//! abstract away the idea of depending on specific implementations of the
//! parser or typechecker and just use a common trait interface that can be
//! used. This file also has definitions for how to access sources whether
//! module or interactive.
pub mod fs;
pub mod settings;
pub mod sources;
pub mod traits;

use std::{collections::HashMap, env, time::Duration};

use fs::{read_in_path, resolve_path};
use hash_ast::{ast::OwnsAstNode, tree::AstTreeGenerator, visitor::AstVisitor};
use hash_reporting::{report::Report, writer::ReportWriter};
use hash_source::SourceId;
use hash_utils::{path::adjust_canonicalization, timed, tree_writing::TreeWriter};
use settings::{CompilerJobParams, CompilerMode, CompilerSettings};
use sources::{Module, Sources};
use traits::{Desugar, Parser, SemanticPass, Tc, VirtualMachine};

pub type CompilerResult<T> = Result<T, Vec<Report>>;

/// The Hash Compiler interface. This interface allows a caller to create a
/// [Compiler] with the specified components. This allows external tinkerers
/// to add their own implementations of each compiler stage with relative ease
/// instead of having to scratch their heads.
pub struct Compiler<'pool, P, D, S, C, V> {
    /// The parser stage of the compiler.
    parser: P,
    /// De-sugar the AST
    desugarer: D,
    /// Perform semantic analysis on the AST.
    semantic_analyser: S,
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
    V: VirtualMachine<'c>,
> {
    /// The collected workspace sources for the current job.
    pub sources: Sources,
    /// Any diagnostics that were collected from any stage
    pub diagnostics: Vec<Report>,
    /// The typechecker state.
    pub ds_state: D::State,
    /// The semantic analysis state.
    pub semantic_analysis_state: S::State,
    /// The typechecker state.
    pub tc_state: C::State,
    /// The State of the Virtual machine
    pub vm_state: V::State,
}

impl<'c, 'pool, P, D, S, C, V> Compiler<'pool, P, D, S, C, V>
where
    'pool: 'c,
    P: Parser<'pool>,
    D: Desugar<'pool>,
    S: SemanticPass<'pool>,
    C: Tc<'c>,
    V: VirtualMachine<'c>,
{
    /// Create a new instance of a [Compiler] with the provided parser and
    /// typechecker implementations.
    pub fn new(
        parser: P,
        desugarer: D,
        semantic_analyser: S,
        checker: C,
        vm: V,
        pool: &'pool rayon::ThreadPool,
        settings: CompilerSettings,
    ) -> Self {
        Self {
            parser,
            desugarer,
            semantic_analyser,
            checker,
            /// monomorphisation + lowering
            /// ir
            vm,
            settings,
            pool,
            metrics: HashMap::new(),
        }
    }

    /// Create a compiler state to accompany with compiler execution.
    /// Internally, this calls the [Tc] state making functions and saves it
    /// into the created [CompilerState].
    pub fn create_state(&mut self) -> CompilerResult<CompilerState<'c, 'pool, D, S, C, V>> {
        let sources = Sources::new();
        // let checker_interactive_state = self.checker.make_interactive_state(&mut
        // checker_state)?; let checker_module_state =
        // self.checker.make_module_state(&mut checker_state)?;

        let ds_state = self.desugarer.make_state()?;
        let semantic_analysis_state = self.semantic_analyser.make_state()?;
        let tc_state = self.checker.make_state()?;
        let vm_state = self.vm.make_state()?;

        Ok(CompilerState {
            sources,
            diagnostics: vec![],
            semantic_analysis_state,
            tc_state,
            ds_state,
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

        log::info!("compiler pipeline timings:");

        for (stage, duration) in timings {
            // This shouldn't occur as we don't record this metric in this way
            if *stage == CompilerMode::Full {
                continue;
            }
            total += *duration;

            println!("{: <12}: {duration:?}", format!("{}", stage));
        }

        // Now print the total
        println!("{: <12}: {total:?}\n", format!("{}", CompilerMode::Full));
    }

    /// Utility function used by AST like stages in order to print the
    /// current [Sources].
    fn print_sources(&self, sources: &Sources, entry_point: SourceId) {
        match entry_point {
            SourceId::Interactive(id) => {
                // If this is an interactive statement, we want to print the statement that was
                // just parsed.
                let source = sources.node_map().get_interactive_block(id);

                let tree = AstTreeGenerator.visit_body_block(&(), source.node_ref()).unwrap();

                println!("{}", TreeWriter::new(&tree));
            }
            SourceId::Module(_) => {
                // If this is a module, we want to print all of the generated modules from the
                // parsing stage
                for (_, generated_module) in sources.node_map().iter_modules() {
                    let tree =
                        AstTreeGenerator.visit_module(&(), generated_module.node_ref()).unwrap();

                    println!(
                        "Tree for `{}`:\n{}",
                        adjust_canonicalization(generated_module.path()),
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
            self.print_sources(sources, entry_point);
        }

        Ok(())
    }

    /// De-sugaring stage within the pipeline.
    fn desugar_sources(
        &mut self,
        entry_point: SourceId,
        sources: &mut Sources,
        desugar_state: &mut D::State,
        job_params: &CompilerJobParams,
    ) -> CompilerResult<()> {
        timed(
            || self.desugarer.desugar(entry_point, sources, desugar_state, self.pool),
            log::Level::Debug,
            |time| {
                self.metrics.insert(CompilerMode::DeSugar, time);
            },
        )?;

        // We want to loop through all of the generated modules and print
        // the resultant AST
        if job_params.mode == CompilerMode::DeSugar && job_params.output_stage_result {
            self.print_sources(sources, entry_point);
        }

        Ok(())
    }

    /// Semantic pass stage within the pipeline.
    fn perform_semantic_pass(
        &mut self,
        entry_point: SourceId,
        sources: &mut Sources,
        semantic_analyser_state: &mut S::State,
        _job_params: &CompilerJobParams,
    ) -> Result<(), Vec<Report>> {
        timed(
            || {
                self.semantic_analyser.perform_pass(
                    entry_point,
                    sources,
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
    fn typecheck_source(
        &mut self,
        entry_point: SourceId,
        sources: &mut Sources,
        checker_state: &mut C::State,
        job_params: &CompilerJobParams,
    ) -> CompilerResult<()> {
        match entry_point {
            SourceId::Interactive(id) => {
                timed(
                    || self.checker.check_interactive(id, sources, checker_state, job_params),
                    log::Level::Debug,
                    |time| {
                        self.metrics.insert(CompilerMode::Typecheck, time);
                    },
                )?;
            }
            SourceId::Module(id) => {
                timed(
                    || self.checker.check_module(id, sources, checker_state, job_params),
                    log::Level::Debug,
                    |time| {
                        self.metrics.insert(CompilerMode::Typecheck, time);
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
        compiler_state: &mut CompilerState<'c, 'pool, D, S, C, V>,
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

    /// Run a particular job within the pipeline. This function handles both
    /// cases of either the entry point being an [InteractiveId] or a
    /// [ModuleId]. The function deals with executing the required stages in
    /// order as specified by the `job_parameters`
    fn run_pipeline(
        &mut self,
        entry_point: SourceId,
        compiler_state: &mut CompilerState<'c, 'pool, D, S, C, V>,
        job_params: CompilerJobParams,
    ) -> Result<(), ()> {
        let result = self.parse_source(entry_point, &mut compiler_state.sources, &job_params);
        self.maybe_terminate(result, compiler_state, &job_params, CompilerMode::Parse)?;

        let result = self.desugar_sources(
            entry_point,
            &mut compiler_state.sources,
            &mut compiler_state.ds_state,
            &job_params,
        );
        self.maybe_terminate(result, compiler_state, &job_params, CompilerMode::DeSugar)?;

        // Now perform the semantic pass on the sources
        let result = self.perform_semantic_pass(
            entry_point,
            &mut compiler_state.sources,
            &mut compiler_state.semantic_analysis_state,
            &job_params,
        );
        self.maybe_terminate(result, compiler_state, &job_params, CompilerMode::Typecheck)?;

        let result = self.typecheck_source(
            entry_point,
            &mut compiler_state.sources,
            &mut compiler_state.tc_state,
            &job_params,
        );
        self.maybe_terminate(result, compiler_state, &job_params, CompilerMode::Typecheck)?;

        Ok(())
    }

    /// Run a job within the compiler pipeline with the provided state, entry
    /// point and the specified job parameters.
    pub fn run(
        &mut self,
        entry_point: SourceId,
        mut compiler_state: CompilerState<'c, 'pool, D, S, C, V>,
        job_params: CompilerJobParams,
    ) -> CompilerState<'c, 'pool, D, S, C, V> {
        let result = self.run_pipeline(entry_point, &mut compiler_state, job_params);

        // we can print the diagnostics here
        if !compiler_state.diagnostics.is_empty() || result.is_err() {
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

                eprintln!("{}", ReportWriter::new(diagnostic, compiler_state.sources.source_map()));
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

    pub fn run_on_filename(
        &mut self,
        filename: String,
        mut compiler_state: CompilerState<'c, 'pool, D, S, C, V>,
        job_params: CompilerJobParams,
    ) -> CompilerState<'c, 'pool, D, S, C, V> {
        // First we have to work out if we need to transform the path
        let current_dir = env::current_dir().unwrap();
        let filename = resolve_path(filename, current_dir, None);

        if let Err(err) = filename {
            eprintln!(
                "{}",
                ReportWriter::new(err.create_report(), compiler_state.sources.source_map())
            );

            return compiler_state;
        };

        let filename = filename.unwrap();
        let contents = read_in_path(&filename);

        if let Err(err) = contents {
            eprintln!(
                "{}",
                ReportWriter::new(err.create_report(), compiler_state.sources.source_map())
            );

            return compiler_state;
        };

        // Create the entry point and run!
        let entry_point =
            compiler_state.sources.add_module(contents.unwrap(), Module::new(filename));
        self.run(SourceId::Module(entry_point), compiler_state, job_params)
    }
}
