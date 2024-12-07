//! Contains all of the logic and utilities that surround the
//! MSVC linker.

use std::{ffi::OsString, path::Path};

use hash_pipeline::settings::{CompilerSettings, OptimisationLevel};

use super::{LinkOutputKind, Linker};
use crate::command::LinkCommand;

pub struct MsvcLinker<'ctx> {
    /// The command that is being built up for the
    /// link line.
    pub command: LinkCommand,

    /// The compiler session that this linker is using
    /// to link the binary. This provides information about
    /// the target, any specified compiler options, etc.
    pub settings: &'ctx CompilerSettings,
}

impl Linker for MsvcLinker<'_> {
    fn cmd(&mut self) -> &mut LinkCommand {
        &mut self.command
    }

    fn set_output_kind(&mut self, _: LinkOutputKind) {
        // We don't have to anything for the MSVC linker, @@Future: however
        // when we add dynamic/static library building, we need to
        // deal with specifying the filename here.
    }

    fn set_output_filename(&mut self, filename: &Path) {
        let mut arg = OsString::from("/OUT:");
        arg.push(filename);
        self.command.arg(&arg);
    }

    fn link_dylib(&mut self, lib: &str, verbatim: bool, _: bool) {
        self.command.arg(format!("{}{}", lib, if verbatim { "" } else { ".lib" }));
    }

    fn link_static_lib(&mut self, lib: &str, verbatim: bool) {
        self.command.arg(format!("{}{}", lib, if verbatim { "" } else { ".lib" }));
    }

    fn include_path(&mut self, path: &Path) {
        let mut arg = OsString::from("/LIBPATH:");
        arg.push(path);
        self.command.arg(&arg);
    }

    fn add_object(&mut self, path: &Path) {
        self.command.arg(path);
    }

    /// For MSVC, the linker will by default perform the following:
    /// > When used at the command line, the linker defaults to
    /// > /OPT:REF,ICF,LBR. If /DEBUG is specified, the default is
    /// > /OPT:NOREF,NOICF,NOLBR.
    ///
    /// Reference: <https://learn.microsoft.com/en-us/cpp/build/reference/opt-optimizations?view=msvc-170#remarks>
    fn optimize(&mut self) {
        // No-op
    }

    /// For MSVC, specifying that the linker should remove un-used items can
    /// be done via `/OPT:REF` and `/OPT:ICF`. The former removes un-used
    /// functions and data, while the latter removes duplicate functions
    /// and data.
    ///
    /// Documentation for the `/OPT` flag can be found here:
    /// <https://learn.microsoft.com/en-us/cpp/build/reference/opt-optimizations?view=msvc-170>
    fn gc_sections(&mut self) {
        if self.settings.optimisation_level == OptimisationLevel::Debug {
            self.command.arg("/OPT:REF,ICF");
        } else {
            self.command.arg("/OPT:REF,NOICF");
        }
    }
}
