use std::{
    env::{self, current_dir},
    fs::File,
    io::Write,
    ops::{Deref, DerefMut},
    path::Path,
    process::{self, Command, Stdio},
    thread,
};

use hash_messaging::CompilerMessage;
use hash_pipeline::{
    fs::{resolve_path, PRELUDE},
    interface::{CompilerInterface, CompilerResult, CompilerStage},
    settings::CompilerStageKind,
};
use hash_reporting::reporter::Reporter;
use hash_source::{ModuleKind, SourceId};
use hash_utils::{
    indexmap::IndexMap,
    log,
    profiling::{get_resident_set_size, timed, MetricEntry, StageMetrics},
    schemars::schema_for,
    stream::CompilerOutputStream,
    stream_writeln,
};

use crate::metrics::{MetricReporter, Metrics, StageMetricEntry};

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
    metrics: IndexMap<CompilerStageKind, StageMetricEntry>,

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

        Self { compiler, stages, metrics: Metrics::new(), bootstrapping: false }
    }

    /// Function to report the collected metrics on the stages within the
    /// compiler.
    fn report_metrics(&self) {
        log::info!("compiler pipeline metrics:");
        let metrics = MetricReporter::new(&self.metrics);
        let mut stdout = self.compiler.output_stream();
        metrics.report(&mut stdout);
    }

    fn run_stage(&mut self, entry_point: SourceId, index: usize) -> CompilerResult<()> {
        let stage = &mut self.stages[index];
        let stage_kind = stage.kind();
        let start_rss = get_resident_set_size();

        timed(
            || stage.run(entry_point, &mut self.compiler),
            log::Level::Info,
            |time| {
                self.metrics
                    .entry(stage_kind)
                    .and_modify(|prev_time| {
                        prev_time.total.duration += time;
                        prev_time.total.end_rss = get_resident_set_size();
                    })
                    .or_insert_with(|| StageMetricEntry {
                        total: MetricEntry {
                            duration: time,
                            start_rss,
                            end_rss: get_resident_set_size(),
                        },
                        children: StageMetrics::default(),
                    });
            },
        )?;

        self.metrics.entry(stage_kind).and_modify(|entry| entry.children.merge(&stage.metrics()));

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
                panic!(
                    "failed to bootstrap compiler:\n{}",
                    Reporter::from_reports(self.compiler.diagnostics().to_owned())
                );
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
        for diagnostic in self.compiler.diagnostics().iter() {
            if diagnostic.is_error() {
                err_count += 1;
            }

            if diagnostic.is_warning() {
                warn_count += 1;
            }

            stream_writeln!(stderr, "{}", diagnostic);
        }

        // ##Hack: to prevent the compiler from printing this message when the pipeline
        // when it was instructed to terminate before all of the stages. For example, if
        // the compiler is just checking the source, then it will terminate early.
        if err_count != 0 || warn_count != 0 {
            log::info!(
                "compiler terminated with {err_count} error(s), and {warn_count} warning(s)."
            );
        }
    }

    /// Emit a schema for the compiler messaging system.
    pub fn emit_schema(&self) {
        let schema = schema_for!(CompilerMessage);
        let mut stdout = self.compiler.output_stream();
        stream_writeln!(stdout, "{}", serde_json::to_string_pretty(&schema).unwrap());
    }

    /// Run a job within the compiler pipeline with the provided state, entry
    /// point and the specified job parameters.
    pub fn run(&mut self, source: SourceId) {
        let result = self.run_pipeline(source);

        // we can print the diagnostics here
        if self.compiler.settings().emit_errors
            && (!self.compiler.diagnostics().is_empty() || result.is_err())
            && !source.is_prelude()
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
        // Reserve a module id for the module that we are about to add.
        let id = self.workspace_mut().add_module(filename.as_ref().to_path_buf(), kind);
        self.run(id)
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
        let source = self.compiler.workspace_mut().add_interactive_block(input);
        self.run(source)
    }

    /// Potentially run an executable, if the compiler has successfully
    /// compiled an executable.
    pub fn maybe_run_executable(&mut self) {
        let settings = self.compiler.settings();
        let workspace = self.compiler.workspace();

        if settings.stage == CompilerStageKind::Exe
            && workspace.yields_executable(settings)
            && !self.has_errors()
        {
            let path = workspace.executable_path(settings);

            // We need to convert the path to a string so that we can pass it
            // to the `Command` struct.
            let path = path.to_str().unwrap();

            // @@Hack: in order to catch the stderr and or the stdout
            // in the event that we specify a custom stream, we have to create
            // a file-handle, write the contents, and then write the contents
            // that we're captured to the stream. It is messy, but it doesn't
            // seem that the Command interface allows us to specify a custom
            // stream or just some `Write`-able object.
            let capture_stream = |stream: CompilerOutputStream, is_err| {
                match stream {
                    CompilerOutputStream::Stdout(_) | CompilerOutputStream::Stderr(_) => {
                        (Stdio::inherit(), None)
                    }
                    CompilerOutputStream::Owned(_) => {
                        // Create a directory in the `temp` directory that is unique to
                        // the process and the thread that is running the compiler.
                        let mut temp_file = env::temp_dir();
                        temp_file.push(format!(
                            "hash-{}-{}",
                            process::id(),
                            thread::current().id().as_u64()
                        ));

                        // We add the filename based on whether this is stderr, or stdout
                        let name = if is_err { "stderr" } else { "stdout" };
                        temp_file.push(name);

                        // Create the directory and the file
                        std::fs::create_dir_all(temp_file.parent().unwrap()).unwrap_or_else(|_| {
                            panic!("failed to create {} capture directory", name)
                        });
                        let file = File::create(&temp_file)
                            .unwrap_or_else(|_| panic!("failed to create {} capture file", name));
                        (Stdio::from(file), Some(temp_file))
                    }
                }
            };

            let (stdout, stdout_file) = capture_stream(self.compiler.output_stream(), false);
            let (stderr, stderr_file) = capture_stream(self.compiler.error_stream(), true);

            // @@Todo: ideally, we should be able to parse the arguments that are specified
            // after `--` into the spawned process.
            Command::new(path)
                .stdin(Stdio::inherit())
                .stdout(stdout)
                .stderr(stderr)
                .spawn()
                .unwrap()
                .wait()
                .unwrap();

            // Now we have to read the contents of the `stdout` and `stderr` files, and
            // write them to our streams...
            if let Some(stdout_file) = stdout_file
                && let Ok(mut file) = File::open(stdout_file)
            {
                let mut stdout = self.compiler.output_stream();
                std::io::copy(&mut file, &mut stdout).unwrap();
            }

            if let Some(stderr_file) = stderr_file
                && let Ok(mut file) = File::open(stderr_file)
            {
                let mut stderr = self.compiler.error_stream();
                std::io::copy(&mut file, &mut stderr).unwrap();
            }
        }
    }
}
