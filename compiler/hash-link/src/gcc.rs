//! Utilities and an interface to the GCC linker (e.g. `ld`).

use std::process::Command;

use hash_pipeline::settings::CompilerSettings;

use crate::Linker;

pub struct GccLinker<'ctx> {
    /// The command that is being built up for the
    /// link line.
    command: Command,

    /// The compiler session that this linker is using
    /// to link the binary. This provides information about
    /// the target, any specified compiler options, etc.
    session: &'ctx CompilerSettings,
}

impl<'ctx> GccLinker<'ctx> {}

impl<'ctx> Linker for GccLinker<'ctx> {
    fn cmd(&mut self) -> &mut Command {
        todo!()
    }

    fn set_output_kind(&mut self, kind: crate::LinkOutputKind, filename: &std::path::Path) {
        todo!()
    }

    fn set_output_filename(&mut self, filename: &std::path::Path) {
        todo!()
    }

    fn link_dylib(&mut self, lib: &str, verbatim: bool, as_needed: bool) {
        todo!()
    }

    fn link_static_lib(&mut self, lib: &str, verbatim: bool) {
        todo!()
    }

    fn include_path(&mut self, path: &std::path::Path) {
        todo!()
    }

    fn optimize(&mut self) {
        todo!()
    }

    fn gc_sections(&mut self) {
        todo!()
    }
}
