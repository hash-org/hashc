//! Defines a generic linker interface and functions that create
//! an instance of a [Linker] with the provided compiler settings
//! and target options.
#![allow(dead_code)] // @@Temporary: remove when all linker methods are used.

use std::{
    ffi::{OsStr, OsString},
    mem,
    ops::Deref,
    path::Path,
};

use hash_pipeline::{settings::CompilerSettings, workspace::Workspace};
use hash_target::{
    HasTarget, TargetArch,
    link::{Cc, LinkerFlavour, Lld, RelocationModel},
};

use self::{gcc::GccLinker, msvc::MsvcLinker};
use crate::{command::LinkCommand, error::LinkerResult, platform};

pub(crate) mod gcc;
pub(crate) mod mold;
pub(crate) mod msvc;

/// This specifies the kind of output that the linker should
/// produce, whether it is dynamically linked, and whether it
/// should be position-independent or not.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct LinkOutputKind {
    /// Is the output dynamically linked?
    pub is_dynamic: bool,

    /// Is the output position-independent?
    pub is_pic: bool,
}

/// A trait which represents a linker and all of the functionality
/// that a linker should have.
pub trait Linker {
    /// Convert the current linker into a [Command] which can be executed.
    fn cmd(&mut self) -> &mut LinkCommand;

    /// Specify what the linker should output.
    fn set_output_kind(&mut self, kind: LinkOutputKind);

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

    /// Add an object to the linker.
    fn add_object(&mut self, path: &Path);

    /// Specify that the linker should apply optimisation to the
    /// output binary.
    fn optimize(&mut self);

    /// Specify that the linker should enable "garbage collection" of the
    /// output binary.
    ///
    /// In practise this means that the linker will strip all functions
    /// and data that is unreachable from the entry point.
    fn gc_sections(&mut self);

    /// Some linkers use a hint to specify that a library is "dynamic" or
    /// "static", this provides a mechanism to reset that hint for the
    /// next arguments.
    ///
    /// N.B. For most linker wrapper implementations, this does nothing.
    fn reset_per_library_state(&mut self) {}

    /// Specify that the linker should add the "as-needed" flag to the
    /// following libraries that follow in order to try to remove libraries
    /// that aren't used by the binary.
    fn add_as_needed(&mut self) {}
}

impl dyn Linker + '_ {
    /// Add a collection of arguments to the [Linker] instance.
    pub fn args(&mut self, args: impl IntoIterator<Item = impl AsRef<OsStr>>) {
        self.cmd().args(args);
    }

    /// Get the [LinkCommand] from the [Linker].
    pub fn take_command(&mut self) -> LinkCommand {
        mem::replace(self.cmd(), LinkCommand::new(""))
    }
}

/// Using the provided linker path, and the specified [LinkerFlavour], this
/// function will create a [Linker] that can then be used to perform various
/// linking operations.
pub(super) fn get_linker<'a>(
    path: &Path,
    flavour: LinkerFlavour,
    settings: &'a CompilerSettings,
) -> Box<dyn Linker + 'a> {
    // We need to find "link.exe", this is fine to do here since if we can't
    // find link.exe, then this just doesn't return anything.
    let msvc_tool = platform::windows::find_tool(settings.target().name.as_ref(), "link.exe");

    let mut command = match flavour {
        LinkerFlavour::Gnu(Cc::No, Lld::Yes)
        | LinkerFlavour::Darwin(Cc::No, Lld::Yes)
        | LinkerFlavour::Msvc(Lld::Yes) => LinkCommand::lld(path, flavour.lld_flavour()),
        LinkerFlavour::Msvc(Lld::No) => {
            LinkCommand::new(msvc_tool.as_ref().map_or(path, |t| t.path()))
        }
        _ => LinkCommand::new(path),
    };

    let target = settings.target();

    // Due to Windows being crazy^TM, we need tell MSVC to link with the default
    // libraries (vcruntime, msvcrt, etc).
    if flavour.is_msvc_like()
        && let Some(tool) = msvc_tool
    {
        // For UWP(Windows Store) apps, we need to comply with the Windows App
        // Certification Kit, which means that we need to link with the
        // Windows Store libraries.
        if target.vendor == "uwp" {
            let tool_path = tool.path();

            if let Some(root_path) = tool_path.ancestors().nth(4) {
                // We need to add the store library path to the linker search path.
                let arch = match target.arch {
                    TargetArch::X86 => Some("x64"),
                    TargetArch::X86_64 => Some("x86"),
                    TargetArch::Aarch64 => Some("arm64"),
                    TargetArch::Arm => Some("arm"),
                    TargetArch::Unknown => None,
                };

                if let Some(arch_name) = arch {
                    let mut arg = OsString::from("/LIBPATH:");
                    arg.push(format!("{}\\lib\\{}\\store", root_path.display(), arch_name));
                    command.arg(&arg);
                }
            }
        }

        command.args(tool.args());

        // Add any environment variables that the tool provides to our command
        for (key, value) in tool.env() {
            command.env(key, value);
        }
    }

    // @@Future: we could have a specific way of going to use "lld" directly.
    match flavour {
        LinkerFlavour::Gnu(cc, _) | LinkerFlavour::Darwin(cc, _) => Box::new(GccLinker {
            command,
            settings,
            is_ld: cc == Cc::No,
            is_gnu: flavour.is_gnu_like(),
            static_hint: false,
        }) as Box<dyn Linker>,
        LinkerFlavour::Msvc(_) => Box::new(MsvcLinker { command, settings }) as Box<dyn Linker>,
    }
}

/// Given the [CompilerSettings], the [Workspace], and the specified file
/// path, we create a new linker instance.
pub(crate) fn build_linker_args<'a>(
    linker: &mut dyn Linker,
    flavour: LinkerFlavour,
    settings: &'a CompilerSettings,
    workspace: &Workspace,
    output_filename: &Path,
) -> LinkerResult<'a, LinkCommand> {
    // Compute the output kind from the session
    let target = settings.target();

    let output_kind = LinkOutputKind {
        is_dynamic: target.crt_statically_linked,
        is_pic: matches!(target.relocation_mode, RelocationModel::Pic | RelocationModel::Pie),
    };

    // ------------ Order-independent arguments ------------

    // Now, we add pre-link args, these arguments are considered to be "position"
    // independent and can be added before any other arguments.
    if let Some(args) = target.pre_link_args.get_args(flavour) {
        linker.args(args.iter().map(Deref::deref));
    }

    // ------------ Object code and libraries, order-dependent ------------

    // First, we add all of the objects that we just generated from the
    for object in workspace.code_map.objects() {
        linker.add_object(object);
    }

    // @@Todo: we need to record what libraries are being used by the workspace, and
    // then add them here.

    // ------------ Late order independent options ------------

    // Library linking above uses some global state for things like
    // `-Bstatic`/`-Bdynamic` to make command line shorter, reset it to default
    // here before adding more libraries.
    linker.reset_per_library_state();

    if let Some(args) = target.late_link_args.get_args(flavour) {
        linker.args(args.iter().map(Deref::deref));
    }

    // ------------ Arbitrary order-independent options ------------

    // ##PlatformDependant: This is where we add the platform dependant arguments,
    // e.g. on macOSX targets we add the platform SDK,

    // ------------ Late order-dependent options ------------
    if let Some(args) = target.post_link_args.get_args(flavour) {
        linker.args(args.iter().map(Deref::deref));
    }

    platform::apple::add_sdk(linker, flavour, settings)?;

    linker.set_output_filename(output_filename);
    linker.set_output_kind(output_kind);
    linker.optimize();

    // ------------ Environment Variables ------------

    // Disable localisation on the linker, this causes problems when
    // checking the output of the linker program.
    platform::disable_localisation(linker.cmd());

    for (key, value) in target.link_env.as_ref() {
        linker.cmd().env(key.as_ref(), value.as_ref());
    }

    for key in target.link_env_remove.as_ref() {
        linker.cmd().env_remove(key.as_ref());
    }

    Ok(linker.take_command())
}
