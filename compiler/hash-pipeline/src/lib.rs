//! Hash Compiler pipeline implementation. The pipeline is a abstract
//! representation of the compiler flow managing the compiling steps like
//! parsing, typechecking, optimisation passes, etc. The pipeline is used to
//! abstract away the idea of depending on specific implementations of the
//! parser or typechecker and just use a common trait interface that can be
//! used. This file also has definitions for how to access sources whether
//! module or interactive.
pub mod args;
pub mod error;
pub mod fs;
pub mod interface;
pub mod settings;
pub mod workspace;

use std::{collections::HashMap, env::current_dir, path::Path, time::Duration};

use fs::{read_in_path, resolve_path, PRELUDE};
use hash_ast::node_map::ModuleEntry;
use hash_reporting::{reporter::Reports, writer::ReportWriter};
use hash_source::{ModuleKind, SourceId};
use hash_utils::{log, stream_writeln, timing::timed};
use interface::{CompilerInterface, CompilerStage};
use settings::CompilerStageKind;

pub type CompilerResult<T> = Result<T, Reports>;

/// The Hash Compiler interface. This interface allows a caller to create a
/// [Compiler] with the specified components. This allows external tinkerers
/// to add their own implementations of each compiler stage with relative ease
/// instead of having to scratch their heads.
pub struct Compiler<I: CompilerInterface> {
    /// The attached stages of the compiler pipeline.
    stages: Vec<Box<dyn CompilerStage<I>>>,

    /// A record of all of the stage metrics
    metrics: HashMap<CompilerStageKind, Duration>,

    /// Whether the pipeline is currently bootstrapping, i.e. when
    /// it is running the prelude module in order to place everything
    /// that is required for the core of the language to work.
    bootstrapping: bool,
}

impl<I: CompilerInterface> Compiler<I> {
    /// Create a new instance of a [Compiler] with the provided parser and
    /// typechecker implementations. The provided [CompilerStage]s to the
    /// compiler must be provided in an ascending ord
    ///er of the [CompilerStageKind]. Stages
    ///are allowed to have the same[CompilerStageKind]s,
    ///but this will mean that they are treated as if
    /// they are one stage in some operations.
    pub fn new(stages: Vec<Box<dyn CompilerStage<I>>>) -> Self {
        // Assert that all the provided stages have a correct stage order, as in
        // each stage has the same level or a higher order stage than the previous
        // stage.
        assert!(stages.windows(2).all(|w| w[0].kind() <= w[1].kind()));

        Self { stages, metrics: HashMap::new(), bootstrapping: false }
    }

    /// Function to report the collected metrics on the stages within the
    /// compiler.
    fn report_metrics(&self, ctx: &I) {
        let mut total = Duration::new(0, 0);

        log::info!("compiler pipeline timings:");
        let mut stderr = ctx.error_stream();

        // Get the longest key in the stages
        let longest_key = self
            .stages
            .iter()
            .map(|stage| {
                let label_size = stage.kind().as_str().len();
                stage
                    .metrics()
                    .iter()
                    .map(|(item, _)| label_size + item.len() + 2)
                    .max()
                    .unwrap_or(label_size)
            })
            .max()
            .unwrap_or(0);

        let report_stage_metrics = |stage: &dyn CompilerStage<I>| {
            let mut stderr = ctx.error_stream();
            let kind = stage.kind();

            for (item, duration) in stage.metrics().iter() {
                stream_writeln!(
                    stderr,
                    "{: <width$}: {duration:?}",
                    format!("{kind}::{item}"),
                    width = longest_key
                );
            }
        };

        let mut stages = self.stages.iter().peekable();
        let Some(mut kind) = stages.peek().map(|stage| stage.kind()) else {
            return
        };

        let mut stage_count = 0;

        // Iterate over each stage and print out the timings.
        for stage in stages {
            // This shouldn't occur as we don't record this metric in this way
            if kind == CompilerStageKind::Full {
                continue;
            }

            if stage.kind() == kind {
                // Query if this particular stage has any additional metrics that
                // should be added under this stage, and then skip reporting the
                // sub metrics.
                if stage_count != 0 {
                    stage_count = 1;
                    report_stage_metrics(&**stage);
                    continue;
                }

                stage_count += 1;
            } else {
                stage_count = 1;
                kind = stage.kind();
            }

            let Some(duration) = self.metrics.get(&kind).copied() else {
                continue;
            };

            total += duration;

            stream_writeln!(
                stderr,
                "{: <width$}: {duration:?}",
                format!("{kind}"),
                width = longest_key
            );
            report_stage_metrics(&**stage);
        }

        // Now print the total
        stream_writeln!(
            stderr,
            "{: <width$}: {total:?}\n",
            format!("{}", CompilerStageKind::Full),
            width = longest_key
        );
    }

    fn run_stage(
        &mut self,
        entry_point: SourceId,
        workspace: &mut I,
        index: usize,
    ) -> CompilerResult<()> {
        let stage = &mut self.stages[index];
        let stage_kind = stage.kind();

        timed(
            || stage.run(entry_point, workspace),
            log::Level::Info,
            |time| {
                self.metrics
                    .entry(stage_kind)
                    .and_modify(|prev_time| {
                        *prev_time += time;
                    })
                    .or_insert(time);
            },
        )?;

        // If we are bootstrapping, we don't need to run the cleanup
        // function since it will be invoked by the the second run of
        // the pipeline for the actual compilation.
        if !self.bootstrapping {
            stage.cleanup(entry_point, workspace);
        }

        Ok(())
    }

    /// Helper function in order to check if the pipeline needs to terminate
    /// after any stage that is specified within the settings of the compiler.
    fn maybe_terminate(&self, result: CompilerResult<()>, ctx: &mut I) -> Result<(), ()> {
        if let Err(diagnostics) = result {
            ctx.diagnostics_mut().extend(diagnostics.into_iter());

            // Some diagnostics might not be errors and all just warnings, in this
            // situation, we don't have to terminate execution
            if ctx.diagnostics().iter().any(|r| r.is_error()) {
                return Err(());
            }
        }

        Ok(())
    }

    /// Run a particular job within the pipeline. The function deals with
    /// executing the required stages in order as specified by the
    /// `job_parameters`
    fn run_pipeline(&mut self, entry_point: SourceId, ctx: &mut I) -> Result<(), ()> {
        for stage in 0..self.stages.len() {
            let kind = self.stages[stage].kind();

            // Terminate the pipeline if we have reached a stage that is
            // beyond the currently specified stage.
            if ctx.settings().stage < kind {
                return Err(());
            }

            let result = self.run_stage(entry_point, ctx, stage);
            self.maybe_terminate(result, ctx)?;
        }

        Ok(())
    }

    /// Function to bootstrap the pipeline. This function invokes a job within
    /// the pipeline in order to load the prelude before any modules run.
    pub fn bootstrap(&mut self, mut ctx: I) -> I {
        if !ctx.settings().skip_prelude {
            self.bootstrapping = true;

            // Temporarily swap the settings with a patched settings in order
            // for the prelude bootstrap to run
            let stage_kind = ctx.settings_mut().stage;
            ctx.settings_mut().stage = CompilerStageKind::Lower;

            // We don't need to run the prelude in the full pipeline, just until
            // IR-gen since that will be dealt by the actual pipeline.

            // Resolve the current working directory so that we can
            // resolve the prelude path...
            let wd = match current_dir() {
                Ok(wd) => wd,
                Err(err) => {
                    ctx.diagnostics_mut().push(err.into());
                    return ctx;
                }
            };

            let path = match resolve_path(PRELUDE, wd) {
                Ok(path) => path,
                Err(err) => {
                    ctx.diagnostics_mut().push(err.into());
                    return ctx;
                }
            };

            ctx = self.run_on_filename(path, ModuleKind::Prelude, ctx);

            // Reset the settings
            ctx.settings_mut().stage = stage_kind;

            // The prelude shouldn't generate any errors, otherwise we just failed to
            // bootstrap
            if ctx.diagnostics().iter().any(|r| r.is_error()) {
                panic!("failed to bootstrap compiler");
            }

            self.bootstrapping = false;
        }

        ctx
    }

    /// Emit diagnostics to the error stream with the applied settings.
    pub fn emit_diagnostics(&self, ctx: &I) {
        let mut err_count = 0;
        let mut warn_count = 0;
        let mut stderr = ctx.error_stream();

        // @@Copying: Ideally, we would not want to copy here!
        for diagnostic in ctx.diagnostics().iter().cloned() {
            if diagnostic.is_error() {
                err_count += 1;
            }

            if diagnostic.is_warning() {
                warn_count += 1;
            }

            stream_writeln!(stderr, "{}", ReportWriter::single(diagnostic, ctx.source_map()));
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

    /// Run a job within the compiler pipeline with the provided state, entry
    /// point and the specified job parameters.
    pub fn run(&mut self, entry_point: SourceId, mut ctx: I) -> I {
        let result = self.run_pipeline(entry_point, &mut ctx);

        // we can print the diagnostics here
        if ctx.settings().emit_errors && (!ctx.diagnostics().is_empty() || result.is_err()) {
            self.emit_diagnostics(&ctx);
        }

        // Print compiler stage metrics if specified in the settings.
        if ctx.settings().output_metrics && !self.bootstrapping {
            self.report_metrics(&ctx);
        }

        ctx
    }

    /// Run the compiler pipeline on a file specified by the path on the disk.
    /// This essentially performs the required steps of loading in a module
    /// off the disk, store it within the [Workspace] and invoke
    /// [`Self::run`]
    pub fn run_on_filename(
        &mut self,
        filename: impl AsRef<Path>,
        kind: ModuleKind,
        mut ctx: I,
    ) -> I {
        let contents = read_in_path(&filename);

        if let Err(err) = contents {
            ctx.diagnostics_mut().push(err.into());

            // Since this a fatal error because we couldn't read the file, we
            // emit the diagnostics (if specified to emit) and terminate.
            if ctx.settings().emit_errors {
                self.emit_diagnostics(&ctx);
            }

            return ctx;
        };

        // Create the entry point and run!
        let entry_point = ctx.workspace_mut().add_module(
            contents.unwrap(),
            ModuleEntry::new(filename.as_ref().to_path_buf()),
            kind,
        );

        self.run(entry_point, ctx)
    }
}
