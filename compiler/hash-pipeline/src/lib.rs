//! Hash Compiler pipeline implementation. The pipeline is a abstract
//! representation of the compiler flow managing the compiling steps like
//! parsing, typechecking, optimisation passes, etc. The pipeline is used to
//! abstract away the idea of depending on specific implementations of the
//! parser or typechecker and just use a common trait interface that can be
//! used. This file also has definitions for how to access sources whether
//! module or interactive.
pub mod fs;
pub mod interface;
pub mod settings;
pub mod workspace;

use std::{collections::HashMap, env, time::Duration};

use fs::{read_in_path, resolve_path, PRELUDE};
use hash_ast::node_map::ModuleEntry;
use hash_reporting::{report::Report, writer::ReportWriter};
use hash_source::{constant::CONSTANT_MAP, ModuleKind, SourceId};
use hash_utils::timing::timed;
use interface::{CompilerInterface, CompilerStage};
use settings::{CompilerSettings, CompilerStageKind};

pub type CompilerResult<T> = Result<T, Vec<Report>>;

/// The Hash Compiler interface. This interface allows a caller to create a
/// [Compiler] with the specified components. This allows external tinkerers
/// to add their own implementations of each compiler stage with relative ease
/// instead of having to scratch their heads.
pub struct Compiler<W: CompilerInterface> {
    /// The attached stages of the compiler pipeline.
    stages: Vec<Box<dyn CompilerStage<W>>>,

    /// Various settings for the compiler.
    pub settings: CompilerSettings,

    /// A record of all of the stage metrics
    metrics: HashMap<CompilerStageKind, Duration>,
}

impl<W: CompilerInterface> Compiler<W> {
    /// Create a new instance of a [Compiler] with the provided parser and
    /// typechecker implementations. The provided [CompilerStage]s to the
    /// compiler must be provided in an ascending ord
    ///er of the [CompilerStageKind]. Stages
    ///are allowed to have the same[CompilerStageKind]s,
    ///but this will mean that they are treated as if
    /// they are one stage in some operations.
    pub fn new(stages: Vec<Box<dyn CompilerStage<W>>>, settings: CompilerSettings) -> Self {
        // Assert that all the provided stages have a correct stage order, as in
        // each stage has the same level or a higher order stage than the previous
        // stage.
        assert!(stages.windows(2).all(|w| w[0].stage_kind() <= w[1].stage_kind()));

        Self { stages, settings, metrics: HashMap::new() }
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
            if *stage == CompilerStageKind::Full {
                continue;
            }
            total += *duration;

            eprintln!("{: <12}: {duration:?}", format!("{}", stage));
        }

        // Now print the total
        eprintln!("{: <12}: {total:?}\n", format!("{}", CompilerStageKind::Full));
    }

    fn run_stage(
        &mut self,
        entry_point: SourceId,
        workspace: &mut W,
        index: usize,
    ) -> CompilerResult<()> {
        let stage = &mut self.stages[index];
        let stage_kind = stage.stage_kind();

        timed(
            || stage.run_stage(entry_point, workspace),
            log::Level::Debug,
            |time| {
                self.metrics
                    .entry(stage_kind)
                    .and_modify(|prev_time| {
                        *prev_time += time;
                    })
                    .or_insert(time);
            },
        )?;

        // run the cleanup function
        stage.cleanup(entry_point, workspace);
        Ok(())
    }

    /// Helper function in order to check if the pipeline needs to terminate
    /// after any stage that is specified within the settings of the compiler.
    fn maybe_terminate(
        &self,
        result: CompilerResult<()>,
        compiler_state: &mut W,
        current_stage: CompilerStageKind,
    ) -> Result<(), ()> {
        if let Err(diagnostics) = result {
            compiler_state.diagnostics_mut().extend(diagnostics.into_iter());

            // Some diagnostics might not be errors and all just warnings, in this
            // situation, we don't have to terminate execution
            if compiler_state.diagnostics().iter().any(|r| r.is_error()) {
                return Err(());
            }
        }

        // Terminate the pipeline if we have reached the stage regardless of error state
        if self.settings.stage == current_stage {
            return Err(());
        }

        Ok(())
    }

    /// Run a particular job within the pipeline. The function deals with
    /// executing the required stages in order as specified by the
    /// `job_parameters`
    fn run_pipeline(&mut self, entry_point: SourceId, compiler_state: &mut W) -> Result<(), ()> {
        for stage in 0..self.stages.len() {
            let kind = self.stages[stage].stage_kind();

            let result = self.run_stage(entry_point, compiler_state, stage);
            self.maybe_terminate(result, compiler_state, kind)?;
        }

        Ok(())
    }

    /// Function to bootstrap the pipeline. This function invokes a job within
    /// the pipeline in order to load the prelude before any modules run.
    pub fn bootstrap(&mut self, mut compiler_state: W) -> W {
        if !self.settings.skip_prelude {
            // Temporarily swap the settings with a patched settings in order
            // for the prelude bootstrap to run
            let mut old_settings = std::mem::take(&mut self.settings);

            // we need to load in the `prelude` module and have it ready for any other
            // sources
            compiler_state =
                self.run_on_filename(PRELUDE.to_string(), ModuleKind::Prelude, compiler_state);

            // Reset the settings
            std::mem::swap(&mut self.settings, &mut old_settings);

            // The prelude shouldn't generate any errors, otherwise we just failed to
            // bootstrap
            if compiler_state.diagnostics().iter().any(|r| r.is_error()) {
                panic!("Failed to bootstrap compiler");
            }
        }

        compiler_state
    }

    /// Run a job within the compiler pipeline with the provided state, entry
    /// point and the specified job parameters.
    pub fn run(&mut self, entry_point: SourceId, mut compiler_state: W) -> W {
        let result = self.run_pipeline(entry_point, &mut compiler_state);

        // we can print the diagnostics here
        if self.settings.emit_errors
            && (!compiler_state.diagnostics().is_empty() || result.is_err())
        {
            let mut err_count = 0;
            let mut warn_count = 0;

            // @@Copying: Ideally, we would not want to copy here!
            for diagnostic in compiler_state.diagnostics().iter().cloned() {
                if diagnostic.is_error() {
                    err_count += 1;
                }

                if diagnostic.is_warning() {
                    warn_count += 1;
                }

                eprintln!("{}", ReportWriter::new(diagnostic, compiler_state.source_map()));
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
        if self.settings.output_metrics {
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
        mut compiler_state: W,
    ) -> W {
        // First we have to work out if we need to transform the path
        let current_dir = env::current_dir().unwrap();

        let path = CONSTANT_MAP.create_string(filename.into().as_str());
        let filename = resolve_path(path, current_dir);

        if let Err(err) = filename {
            compiler_state.diagnostics_mut().push(err.create_report());

            // Only print the error if specified within the settings
            if self.settings.emit_errors {
                eprintln!(
                    "{}",
                    ReportWriter::new(err.create_report(), compiler_state.source_map())
                );
            }

            return compiler_state;
        };

        let filename = filename.unwrap();
        let contents = read_in_path(&filename);

        if let Err(err) = contents {
            compiler_state.diagnostics_mut().push(err.create_report());

            // Only print the error if specified within the settings
            if self.settings.emit_errors {
                eprintln!(
                    "{}",
                    ReportWriter::new(err.create_report(), compiler_state.source_map())
                );
            }

            return compiler_state;
        };

        // Create the entry point and run!

        let entry_point = compiler_state.workspace_mut().add_module(
            contents.unwrap(),
            ModuleEntry::new(filename),
            kind,
        );

        self.run(SourceId::Module(entry_point), compiler_state)
    }
}
