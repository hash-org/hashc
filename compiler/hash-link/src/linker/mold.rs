//! A wrapper around the [`mold`](https://github.com/rui314/mold) linker. Mold
//! is an open source linker that is designed to be fast and small. It is
//! written in C++ and is a drop-in replacement for Unix systems.
//!
//! Currently, it is assumed that the `mold` linker is used on Linux
//! systems.

use std::{ffi::OsStr, path::Path};

use hash_pipeline::settings::{CompilerSettings, OptimisationLevel};

use super::{LinkOutputKind, Linker};
use crate::command::LinkCommand;

pub struct MoldLinker<'ctx> {
    /// The command that is being built up for the
    /// link line.
    command: LinkCommand,

    /// The [CompilerSettings] that this linker is using
    /// to link the binary. This provides information about
    /// the target, any specified compiler options, etc.
    settings: &'ctx CompilerSettings,
}

impl<'ctx> MoldLinker<'ctx> {
    /// Passes a collection of argument directly to the linker.
    fn linker_args(&mut self, args: &[impl AsRef<OsStr>]) -> &mut Self {
        args.iter().for_each(|arg| {
            self.command.arg(arg);
        });

        self
    }
}

impl<'ctx> Linker for MoldLinker<'ctx> {
    fn cmd(&mut self) -> &mut LinkCommand {
        &mut self.command
    }

    fn set_output_kind(&mut self, kind: LinkOutputKind) {
        if kind.is_pic {
            self.command.arg("--pic");
        } else {
            self.command.arg("--no-pic");
        }

        // @@Investigate: do we need to set anything for dynamic?
        if !kind.is_dynamic {
            self.command.arg("--static");
        }
    }

    fn set_output_filename(&mut self, filename: &Path) {
        self.command.arg("-o").arg(filename);
    }

    fn link_dylib(&mut self, lib: &str, _: bool, as_needed: bool) {
        if as_needed {
            self.linker_args(&["--push-state", "--as-needed"]);
        }

        self.command.arg(format!("-l{lib}"));

        // If we set `as_needed` we now need "pop" the state in
        // the linker
        if as_needed {
            self.command.arg("--pop-state");
        }
    }

    fn link_static_lib(&mut self, lib: &str, _: bool) {
        self.command.arg(format!("-l{lib}"));
    }

    fn include_path(&mut self, path: &Path) {
        self.command.arg("-L").arg(path);
    }

    fn add_object(&mut self, path: &Path) {
        self.command.arg(path);
    }

    fn optimize(&mut self) {
        if self.settings.optimisation_level > OptimisationLevel::Debug {
            self.command.arg("-O1");
        }
    }

    fn gc_sections(&mut self) {
        self.command.arg("--gc-sections");
    }
}
