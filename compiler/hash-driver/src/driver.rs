use std::{
    collections::HashMap,
    env::current_dir,
    ops::{Deref, DerefMut},
    path::Path,
    time::Duration,
};

use hash_ast::node_map::{InteractiveBlock, ModuleEntry};
use hash_pipeline::{
    fs::{read_in_path, resolve_path, PRELUDE},
    interface::{CompilerInterface, CompilerResult, CompilerStage},
    settings::CompilerStageKind,
};
use hash_reporting::writer::ReportWriter;
use hash_source::{ModuleKind, SourceId};
use hash_utils::{log, stream_writeln, timing::timed};

/// The Hash Compiler interface. This interface allows a caller to create a
/// [Driver] with a `compiler` and a collection of stages which will access
/// information from the `compiler` via a [CompilerInterface] or a more
/// specific interface.
///
/// @@Future: This should allow external tinkerers to add their own
/// implementations of each compiler stage with relative ease instead of having
/// to scratch their heads. However, it is still somewhat unclear how to make
/// this as convenient as possible.
pub struct Driver<I: CompilerInterface> {
    /// The session that the compiler is running in.
    compiler: I,

    /// The attached stages of the compiler pipeline.
    stages: Vec<Box<dyn CompilerStage<I>>>,

    /// A record of all of the stage metrics
    metrics: HashMap<CompilerStageKind, Duration>,

    /// Whether the pipeline is currently bootstrapping, i.e. when
    /// it is running the prelude module in order to place everything
    /// that is required for the core of the language to work.
    bootstrapping: bool,
}

impl<I: CompilerInterface> Deref for Driver<I> {
    type Target = I;

    fn deref(&self) -> &Self::Target {
        &self.compiler
    }
}

impl<I: CompilerInterface> DerefMut for Driver<I> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.compiler
    }
}

impl<I: CompilerInterface> Driver<I> {
    /// Create a new instance of a [Compiler] with the provided parser and
    /// typechecker implementations. The provided [CompilerStage]s to the
    /// compiler must be provided in an ascending ord
    ///er of the [CompilerStageKind]. Stages
    ///are allowed to have the same[CompilerStageKind]s,
    ///but this will mean that they are treated as if
    /// they are one stage in some operations.
    pub fn new(compiler: I, stages: Vec<Box<dyn CompilerStage<I>>>) -> Self {
        // Assert    that all the provided stages have a correct stage order, as in
        // each stage has the same level or a higher order stage than the previous
        // stage.
        assert!(stages.windows(2).all(|w| w[0].kind() <= w[1].kind()));

        Self { compiler, stages, metrics: HashMap::new(), bootstrapping: false }
    }

    /// Function to report the collected metrics on the stages within the
    /// compiler.
    fn report_metrics(&self) {
        let mut total = Duration::new(0, 0);

        log::info!("compiler pipeline timings:");
        let mut stderr = self.compiler.error_stream();

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
            let mut stderr = self.compiler.error_stream();
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
        let Some(mut kind) = stages.peek().map(|stage| stage.kind()) else { return };

        let mut stage_count = 0;

        // Iterate over each stage and print out the timings.
        for stage in stages {
            // This shouldn't occur as we don't record this metric in this way
            if kind >= CompilerStageKind::Build {
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
            format!("{}", CompilerStageKind::Build),
            width = longest_key
        );
    }

    fn run_stage(&mut self, entry_point: SourceId, index: usize) -> CompilerResult<()> {
        let stage = &mut self.stages[index];
        let stage_kind = stage.kind();

        timed(
            || stage.run(entry_point, &mut self.compiler),
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
            stage.cleanup(entry_point, &mut self.compiler);
        }

        Ok(())
    }

    /// Helper function in order to check if the pipeline needs to terminate
    /// after any stage that is specified within the settings of the compiler.
    fn maybe_terminate(&mut self, result: CompilerResult<()>) -> Result<(), ()> {
        if let Err(diagnostics) = result {
            self.compiler.diagnostics_mut().extend(diagnostics);

            // Some diagnostics might not be errors and all just warnings, in this
            // situation, we don't have to terminate execution
            if self.compiler.diagnostics().iter().any(|r| r.is_error()) {
                return Err(());
            }
        }

        Ok(())
    }

    /// Run a particular job within the pipeline. The function deals with
    /// executing the required stages in order as specified by the
    /// `job_parameters`
    fn run_pipeline(&mut self, entry_point: SourceId) -> Result<(), ()> {
        for stage in 0..self.stages.len() {
            let kind = self.stages[stage].kind();

            // Terminate the pipeline if we have reached a stage that is
            // beyond the currently specified stage.
            if self.compiler.settings().stage < kind {
                return Err(());
            }

            let result = self.run_stage(entry_point, stage);
            self.maybe_terminate(result)?;
        }

        Ok(())
    }

    /// Function to bootstrap the pipeline. This function invokes a job within
    /// the pipeline in order to load the prelude before any modules run.
    pub fn bootstrap(&mut self) {
        if !self.compiler.settings().skip_prelude {
            self.bootstrapping = true;

            // Temporarily swap the settings with a patched settings in order
            // for the prelude bootstrap to run
            let stage_kind = self.compiler.settings_mut().stage;
            self.compiler.settings_mut().stage = CompilerStageKind::Analysis;

            // We don't need to run the prelude in the full pipeline, just until
            // IR-gen since that will be dealt by the actual pipeline.

            // Resolve the current working directory so that we can
            // resolve the prelude path...
            let wd = match current_dir() {
                Ok(wd) => wd,
                Err(err) => {
                    self.compiler.diagnostics_mut().push(err.into());
                    return;
                }
            };

            let path = match resolve_path(PRELUDE, wd) {
                Ok(path) => path,
                Err(err) => {
                    self.compiler.diagnostics_mut().push(err.into());
                    return;
                }
            };

            self.run_filename(path, ModuleKind::Prelude);

            // Reset the settings
            self.compiler.settings_mut().stage = stage_kind;

            // The prelude shouldn't generate any errors, otherwise we just failed to
            // bootstrap
            if self.compiler.diagnostics().iter().any(|r| r.is_error()) {
                panic!("failed to bootstrap compiler");
            }

            self.bootstrapping = false;
        }
    }

    /// Emit diagnostics to the error stream with the applied settings.
    pub fn emit_diagnostics(&self) {
        let mut err_count = 0;
        let mut warn_count = 0;
        let mut stderr = self.compiler.error_stream();

        // @@Copying: Ideally, we would not want to copy here!
        for diagnostic in self.compiler.diagnostics().iter().cloned() {
            if diagnostic.is_error() {
                err_count += 1;
            }

            if diagnostic.is_warning() {
                warn_count += 1;
            }

            stream_writeln!(
                stderr,
                "{}",
                ReportWriter::single(diagnostic, self.compiler.source_map())
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

    /// Run a job within the compiler pipeline with the provided state, entry
    /// point and the specified job parameters.
    pub fn run(&mut self, source: SourceId) {
        let result = self.run_pipeline(source);

        // we can print the diagnostics here
        if self.compiler.settings().emit_errors
            && (!self.compiler.diagnostics().is_empty() || result.is_err())
        {
            self.emit_diagnostics();
        }

        // Print compiler stage metrics if specified in the settings.
        if self.compiler.settings().show_timings && !self.bootstrapping {
            self.report_metrics();
        }
    }

    /// Run the compiler pipeline on a file specified by the path on the disk.
    /// This essentially performs the required steps of loading in a module
    /// off the disk, store it within the [Workspace] and invoke
    /// [`Self::run`]
    pub fn run_filename(&mut self, filename: impl AsRef<Path>, kind: ModuleKind) {
        let contents = read_in_path(&filename);

        if let Err(err) = contents {
            self.compiler.diagnostics_mut().push(err.into());

            // Since this a fatal error because we couldn't read the file, we
            // emit the diagnostics (if specified to emit) and terminate.
            if self.compiler.settings().emit_errors {
                self.emit_diagnostics();
            }

            return;
        };

        // Create the module and run!
        let module = self.compiler.workspace_mut().add_module(
            contents.unwrap(),
            ModuleEntry::new(filename.as_ref().to_path_buf()),
            kind,
        );

        self.run(module)
    }

    /// Run the compiler pipeline on the entry point specified in the settings.
    pub fn run_on_entry_point(&mut self) {
        match self.compiler.settings().entry_point() {
            Ok(entry_point) => self.run_filename(entry_point, ModuleKind::EntryPoint),
            Err(err) => {
                self.compiler.diagnostics_mut().push(err.into());

                if self.compiler.settings().emit_errors {
                    self.emit_diagnostics();
                }
            }
        }
    }

    /// Run the compiler on a interactive line input.
    pub fn run_interactive(&mut self, input: String) {
        let source = self.compiler.add_interactive_block(input, InteractiveBlock::new());
        self.run(source)
    }
}
