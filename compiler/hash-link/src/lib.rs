//! This crate contains all of the logic surrounding a linker
//! interface. This provides a generic [Linker] trait which is then
//! implemented by several linker flavours (e.g. `msvc` and `lld`)
#![allow(unused)]

pub mod gcc;
pub mod lld;
pub mod mold;
pub mod msvc;

use std::{
    io,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use hash_pipeline::{
    interface::{CompilerInterface, CompilerOutputStream, CompilerStage},
    settings::{CompilerSettings, CompilerStageKind},
    workspace::Workspace,
    CompilerResult,
};
use hash_source::SourceId;
use hash_target::link::{Cc, LinkerFlavour, Lld};

/// This specifies the kind of output that the linker should
/// produce, whether it is dynamically linked, and whether it
/// should be position-independent or not.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct LinkOutputKind {
    /// Is the output dynamically linked?
    pub dynamic: bool,

    /// Is the output position-independent?
    pub is_pic: bool,
}

/// A trait which represents a linker and all of the functionality
/// that a linker should have.
pub trait Linker {
    /// Convert the current linker into a [Command] which can be executed.
    fn cmd(&mut self) -> &mut Command;

    /// Specify what the linker should output.
    fn set_output_kind(&mut self, kind: LinkOutputKind, filename: &Path);

    /// Specify the output filename.
    fn set_output_filename(&mut self, filename: &Path);

    /// Link a dynamic library. If the `verbatim` flag is specified, this
    /// will append the appropriate suffix to the library name.
    ///
    /// If the `as_needed` flag is specified, the linker will only link the
    /// library if it is needed. This flag is only relevant to the `GCC` linker.
    fn link_dylib(&mut self, lib: &str, verbatim: bool, as_needed: bool);

    /// Link a static library. If the `verbatim` flag is specified, this
    /// will append the appropriate suffix to the library name.
    fn link_static_lib(&mut self, lib: &str, verbatim: bool);

    /// Specify a library search path to the linker.    
    fn include_path(&mut self, path: &Path);

    /// Specify that the linker should apply optimisation to the
    /// output binary.
    fn optimize(&mut self);

    /// Specify that the linker should enable "garbage collection" of the
    /// output binary.
    ///
    /// In practise this means that the linker will strip all functions
    /// and data that is unreachable from the entry point.
    fn gc_sections(&mut self);
}

/// The linking context, which contains all of the information
/// from the [CompilerSession] in order to perform
/// the linking of an executable, or library.
pub struct LinkerCtx<'ctx> {
    /// Reference to the current compiler workspace.
    pub workspace: &'ctx Workspace,

    /// A reference to the backend settings in the current session.
    pub settings: &'ctx CompilerSettings,

    /// Reference to the output stream
    pub stdout: CompilerOutputStream,
}

pub struct CompilerLinker;

pub trait LinkerCtxQuery: CompilerInterface {
    fn data(&mut self) -> LinkerCtx<'_>;
}

impl<Ctx: LinkerCtxQuery> CompilerStage<Ctx> for CompilerLinker {
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::Link
    }

    fn run(&mut self, _: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let LinkerCtx { workspace, settings, stdout } = ctx.data();

        // If we are not emitting an executable, then we can
        if !workspace.yields_executable(settings) {
            return Ok(());
        }

        // Get the executable path that is going to be
        // emitted by the compiler.
        let output_path = workspace.executable_path();
        let temp_path = workspace.temporary_storage("link").map_err(|err| vec![err.into()])?;

        // Get the linker that is going to be used to link

        let (linker_path, flavour) = get_linker_and_flavour(settings);
        let mut linker = get_linker_with_args(settings, workspace);

        // @@Todo: print out link-line if specified via `-Cemit=link-line`

        // Run the linker
        let command = linker.cmd();
        let program = execute_linker(settings, command, output_path.as_path(), temp_path.as_path());

        Ok(())
    }
}

/// Function which resolves which linker to use given the current [Target]
/// and linker flavour. If the linker cannot be resolved for the current
/// configuration settings, the function will panic.
///
/// @@Future: allow user to specify which linker to use when linking.
fn get_linker_and_flavour(settings: &CompilerSettings) -> (PathBuf, LinkerFlavour) {
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

fn get_linker_with_args(settings: &CompilerSettings, workspace: &Workspace) -> Box<dyn Linker> {
    todo!()
}

fn execute_linker(
    settings: &CompilerSettings,
    cmd: &Command,
    out_filename: &Path,
    temp_dir: &Path,
) -> io::Result<Output> {
    todo!()
}
