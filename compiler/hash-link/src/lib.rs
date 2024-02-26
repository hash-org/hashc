//! This crate contains all of the logic surrounding a linker
//! interface. This provides a generic [crate::linker::Linker] trait which is
//! then implemented by several linker flavours (e.g. `msvc` and `lld`)

pub(crate) mod command;
pub(crate) mod error;
pub(crate) mod linker;
pub(crate) mod platform;

use std::{
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
    process::{Output, Stdio},
};

use command::{EscapeArg, LinkCommand};
use error::{escape_returned_error, AdditionalFailureInfo, LinkerError};
use hash_pipeline::{
    interface::{
        CompilerInterface, CompilerOutputStream, CompilerResult, CompilerStage, StageMetrics,
    },
    settings::{CompilerSettings, CompilerStageKind},
    workspace::Workspace,
};
use hash_source::SourceId;
use hash_target::{
    link::{Cc, LinkerFlavour, Lld},
    HasTarget,
};
use hash_utils::profiling::HasMutMetrics;
use linker::{build_linker_args, get_linker};
use platform::flush_linked_file;

/// The linking context, which contains all of the information
/// from the [DefaultCompilerInterface] in order to perform
/// the linking of an executable, or library.
pub struct LinkerCtx<'ctx> {
    /// Reference to the current compiler workspace.
    pub workspace: &'ctx Workspace,

    /// A reference to the backend settings in the current session.
    pub settings: &'ctx CompilerSettings,

    /// Reference to the output stream
    pub stdout: CompilerOutputStream,
}

/// The Hash compiler linking stage. This stage is responsible for
/// linking all of the object files, libraries and various other
/// artifacts into a single executable or a library.
#[derive(Default)]
pub struct CompilerLinker {
    /// The metrics for this stage. This records the timings
    /// of various operations that the linker performs, including
    /// finding the linker tool, linking, and finally writing the
    /// artifacts to disk.
    metrics: StageMetrics,
}

impl HasMutMetrics for CompilerLinker {
    fn metrics(&mut self) -> &mut StageMetrics {
        &mut self.metrics
    }
}

pub trait LinkerCtxQuery: CompilerInterface {
    fn data(&mut self) -> LinkerCtx<'_>;
}

impl<Ctx: LinkerCtxQuery> CompilerStage<Ctx> for CompilerLinker {
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::Link
    }

    fn metrics(&self) -> StageMetrics {
        self.metrics.clone()
    }

    fn reset_metrics(&mut self) {
        self.metrics = StageMetrics::default();
    }

    fn run(&mut self, _: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let LinkerCtx { workspace, settings, mut stdout } = ctx.data();

        // If we are not emitting an executable, then we can
        if !workspace.yields_executable(settings) || workspace.code_map.objects().next().is_none() {
            return Ok(());
        }

        // Get the executable path that is going to be
        // emitted by the compiler.
        let output_path = workspace.executable_path(settings);
        let temp_path = workspace.temporary_storage("link").map_err(|err| vec![err.into()])?;

        // Get the linker that is going to be used to link

        let (linker_path, flavour) = get_path_linker_and_flavour(settings);
        let linker = &mut *self.record("find", |_| get_linker(&linker_path, flavour, settings));

        let linker_command =
            build_linker_args(linker, flavour, settings, workspace, output_path.as_path())
                .map_err(|err| vec![err.into()])?;

        // print out link-line if specified via `-Cdump=link-line`
        if settings.codegen_settings.dump_link_line {
            writeln!(stdout, "{linker_command}").map_err(|err| vec![err.into()])?;
        }

        // Run the linker
        let program = self.record("execute", |_| {
            execute_linker(settings, &linker_command, output_path.as_path(), temp_path.as_path())
        });

        // @@Cleanup: would be nice to avoid the `vec![]` everywhere
        match program {
            Ok(program) => {
                if !program.status.success() {
                    let mut output = program.stderr.clone();
                    output.extend_from_slice(&program.stdout);

                    let target = settings.target();
                    let escaped_output = escape_returned_error(&output);

                    // Try and deduce more information about why the linking
                    // process failed, it could be that the user doesn't have
                    // a correct version of MSVC or some other tool couldn't
                    // be found.

                    let additional_info = if let Some(code) = program.status.code() {
                        // @@Incomplete: we need to ensure that it isn't just Windows, but MSVC
                        // specifically.
                        if target.is_like_windows()
                            && linker_path.to_str() == Some("link.exe")
                            // All Microsoft `link.exe` linking error codes are
                            // four digit numbers in the range 1000 to 9999 inclusive
                            //
                            // ref: https://learn.microsoft.com/en-us/cpp/error-messages/tool-errors/linker-tools-errors-and-warnings?view=msvc-170
                            && !(1000..=9999).contains(&code)
                        {
                            // Check if the Visual Studio is installed..
                            let is_vs_installed = platform::windows::is_vs_installed();
                            let has_linker =
                                platform::windows::find_tool(target.name.as_ref(), "link.exe")
                                    .is_some();

                            Some(AdditionalFailureInfo { is_vs_installed, has_linker })
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    // construct the error and report it
                    let command = linker_command.command();
                    let error = LinkerError::LinkingFailed {
                        linker_path: &linker_path,
                        exit_status: program.status,
                        command: &command,
                        escaped_output: &escaped_output,
                        additional_info,
                    };
                    return Err(vec![error.into()]);
                }
            }
            Err(err) => {
                // If we couldn't find the linker in the path, then we
                // emit the "Not Found" error.
                if err.kind() == io::ErrorKind::NotFound {
                    let err = LinkerError::NotFound { path: linker_path };
                    return Err(vec![err.into()]);
                }
            }
        }

        Ok(())
    }
}

/// Function which resolves which linker to use given the current [Target]
/// and linker flavour. If the linker cannot be resolved for the current
/// configuration settings, the function will panic.
///
/// @@Future: allow user to specify which linker to use when linking.
fn get_path_linker_and_flavour(settings: &CompilerSettings) -> (PathBuf, LinkerFlavour) {
    let target_flavour = settings.target().linker_flavour;
    let path = match target_flavour {
        LinkerFlavour::Gnu(Cc::Yes, _) | LinkerFlavour::Darwin(Cc::Yes, _) => PathBuf::from("cc"),
        LinkerFlavour::Gnu(_, Lld::Yes) | LinkerFlavour::Darwin(_, Lld::Yes) => {
            PathBuf::from("lld")
        }
        LinkerFlavour::Gnu(..) | LinkerFlavour::Darwin(..) => PathBuf::from("ld"),
        LinkerFlavour::Msvc(_) => PathBuf::from("link.exe"),
    };

    (path, target_flavour)
}

/// Function that orchestrates executing the [LinkCommand] whilst also dealing
/// with platform specific problems of actually executing the command.
fn execute_linker(
    settings: &CompilerSettings,
    command: &LinkCommand,
    out_filename: &Path,
    temp_dir: &Path,
) -> io::Result<Output> {
    // Due to Windows API `CreateProcessA` having a hard limit when spawning
    // a process (https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-createprocessa),
    // we have to check if it exceeds the spawn limit, then we write the command
    // into arguments and pass it to a file. This is not a problem Unix
    // like systems because they don't have this kind of limit.
    if !command.might_exceed_process_spawn_limit() {
        match command.command().stdout(Stdio::piped()).stderr(Stdio::piped()).spawn() {
            Ok(child) => {
                // wait for the child to finish running... and then
                // flush the generated file onto disk (again this is really only a problem
                // on windows machines).
                let output = child.wait_with_output();
                flush_linked_file(&output, out_filename)?;
                return output;
            }
            Err(ref err) if platform::command_line_too_big(err) => {
                // we don't do anything here and just fallthrough to
                // the case of running it through the file path.
            }
            Err(err) => return Err(err),
        }
    }

    // Here, we fall back to writing the Link-line into a file so that
    // we can avoid running into exceeding the spawn limit.
    let mut arguments = String::new();
    let mut command = command.clone();

    let platform = settings.target().platform;

    for argument in command.take_args() {
        let escaped_arg = EscapeArg { argument: argument.to_str().unwrap(), platform }.to_string();
        arguments.push_str(&escaped_arg);
        arguments.push('\n');
    }

    let file = temp_dir.join("linker-arguments");

    // On Windows, we need to use UTF-16LE encoding to avoid
    // problems with non-ASCII characters.
    let buffer = if platform.is_windows() {
        let mut buffer = Vec::with_capacity((1 + arguments.len()) * 2);

        for c in arguments.encode_utf16() {
            buffer.extend_from_slice(&c.to_le_bytes());
        }

        buffer
    } else {
        arguments.into_bytes()
    };

    // Write to the file
    fs::write(&file, buffer)?;

    // Now re-invoke the linker with the file as the argument.
    command.arg(format!("@{}", file.display()));
    let output = command.output();
    flush_linked_file(&output, out_filename)?;
    output
}
