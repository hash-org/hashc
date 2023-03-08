//! Utilities and an interface to the GCC linker (e.g. `ld`).

use std::{
    ffi::{OsStr, OsString},
    path::Path,
};

use hash_pipeline::settings::{CompilerSettings, OptimisationLevel};

use super::{LinkOutputKind, Linker};
use crate::command::LinkCommand;

/// A wrapper around the Glorious GCC linker.
pub struct GccLinker<'ctx> {
    /// The command that is being built up for the
    /// link line.
    pub command: LinkCommand,

    /// The compiler session that this linker is using
    /// to link the binary. This provides information about
    /// the target, any specified compiler options, etc.
    pub settings: &'ctx CompilerSettings,

    /// Whether or not the linker is `ld` like.
    pub is_ld: bool,

    /// Whether or not the linker is GNU `ld` like.
    pub is_gnu: bool,

    /// What is the current hinting mode on the linker.
    ///
    /// N.B. On some platforms, this flag has no accept as they
    /// don't accept hints.
    pub static_hint: bool,
}

impl<'ctx> GccLinker<'ctx> {
    /// Passes an arbitrary argument directly to the linker.
    fn linker_arg(&mut self, arg: impl AsRef<OsStr>) -> &mut Self {
        self.linker_args(&[arg]);
        self
    }

    /// Passes a collection of argument directly to the linker.
    ///
    /// If the linker is `ld` like, then arguments are simply append to the
    /// command. When the linker is not `ld` like, then the arguments are
    /// joined by commas to form an argument that is prepended with `-Wl,`.
    fn linker_args(&mut self, args: &[impl AsRef<OsStr>]) -> &mut Self {
        if self.is_ld {
            args.iter().for_each(|arg| {
                self.command.arg(arg);
            });
        } else if !args.is_empty() {
            let mut s = OsString::from("-Wl");
            for arg in args {
                s.push(",");
                s.push(arg);
            }
            self.command.arg(s);
        }

        self
    }

    /// Check whether the linker takes hints, specifically:
    ///
    /// - macOS does not take hints since it does not rely on
    /// `binutils` to perform linking.
    fn takes_hints(&self) -> bool {
        self.is_ld && self.is_gnu && !self.settings.target().is_like_osx()
    }

    /// Add a hint to the linker that the next specified library
    /// argument is a static library.
    ///
    /// N.B. This hint is only accepted on some platforms.
    pub fn hint_static(&mut self) {
        if !self.takes_hints() {
            return;
        }

        if !self.static_hint {
            self.linker_arg("-Bstatic");
            self.static_hint = true;
        }
    }

    /// Add a hint to the linker that the next specified library argument
    /// is a dynamic library.
    pub fn hint_dynamic(&mut self) {
        if !self.takes_hints() {
            return;
        }

        if self.static_hint {
            self.linker_arg("-Bdynamic");
            self.static_hint = false;
        }
    }
}

impl<'ctx> Linker for GccLinker<'ctx> {
    fn cmd(&mut self) -> &mut LinkCommand {
        &mut self.command
    }

    fn set_output_kind(&mut self, kind: LinkOutputKind) {
        match (kind.is_dynamic, kind.is_pic) {
            (true, true) => {
                if !self.settings.target().is_like_windows() {
                    self.linker_arg("-pie");
                }
            }
            (true, false) => {
                if !self.is_ld && self.is_gnu {
                    self.command.arg("-no-pie");
                }
            }
            (false, true) => {
                if !self.is_ld {
                    self.command.arg("-static-pie");
                } else {
                    // Clang & GCC pass the `--no-dynamic-linker` flag to `ld` to
                    //suppresses the `INTERP` ELF header specifying dynamic linker,
                    // which is otherwise implicitly injected by ld (but not lld).

                    // The `-z text` flag is used to ensure that everything else
                    // is PIC.
                    self.command.args(["-static", "-pie", "--no-dynamic-linker", "-z", "text"]);
                }
            }
            (false, false) => {
                self.command.arg("-static");

                if !self.is_ld && self.is_gnu {
                    self.command.arg("-no-pie");
                }
            }
        }
    }

    fn add_object(&mut self, path: &Path) {
        self.cmd().arg(path);
    }

    fn set_output_filename(&mut self, filename: &Path) {
        self.command.arg("-o").arg(filename);
    }

    fn link_dylib(&mut self, lib: &str, verbatim: bool, as_needed: bool) {
        // This option affects ELF DT_NEEDED tags for dynamic libraries mentioned on the
        // command line after the --as-needed option. Normally the linker will add a
        // DT_NEEDED tag for each dynamic library mentioned on the command line,
        // regardless of whether the library is actually needed or not. --as-needed
        // causes a DT_NEEDED tag to only be emitted for a library that satisfies an
        // undefined symbol reference from a regular object file or, if the library is
        // not found in the DT_NEEDED lists of other libraries linked up to that point,
        // an undefined symbol reference from another dynamic library. --no-as-needed
        // restores the default behaviour.
        if !as_needed && self.is_gnu && !self.settings.target().is_like_windows() {
            self.linker_arg("--no-as-needed");
        }

        self.hint_dynamic();

        let verbatim_prefix = if verbatim && self.is_gnu { ":" } else { "" };
        self.command.arg(format!("-l{verbatim_prefix}{lib}"));

        // Now disable the --as-needed option again.
        if !as_needed && self.is_gnu && !self.settings.target().is_like_windows() {
            self.linker_arg("--as-needed");
        }
    }

    fn link_static_lib(&mut self, lib: &str, verbatim: bool) {
        self.hint_static();

        let verbatim_prefix = if verbatim && self.is_gnu { ":" } else { "" };
        self.command.arg(format!("-l{verbatim_prefix}{lib}"));
    }

    fn include_path(&mut self, path: &std::path::Path) {
        self.command.arg("-L").arg(path);
    }

    fn optimize(&mut self) {
        if !self.is_gnu {
            return;
        }

        if self.settings.optimisation_level > OptimisationLevel::Debug {
            self.linker_arg("-O1");
        }
    }

    fn gc_sections(&mut self) {
        // This essentially performs dead-code elimination on the
        // resultant binary, removing everything that is not used
        // or can't be reached from "main".
        if self.settings.target().is_like_osx() {
            self.linker_arg("-dead_strip");
        }
    }

    fn reset_per_library_state(&mut self) {
        self.hint_dynamic();
    }
}
