//! A wrapper around the [`mold`](https://github.com/rui314/mold) linker.
#![allow(unused)]

use std::path::Path;

use hash_pipeline::settings::CompilerSettings;

use super::{LinkOutputKind, Linker};
use crate::command::LinkCommand;

pub struct MoldLinker<'ctx> {
    /// The command that is being built up for the
    /// link line.
    command: LinkCommand,

    /// The compiler session that this linker is using
    /// to link the binary. This provides information about
    /// the target, any specified compiler options, etc.
    session: &'ctx CompilerSettings,
}

impl<'ctx> Linker for MoldLinker<'ctx> {
    fn cmd(&mut self) -> &mut LinkCommand {
        &mut self.command
    }

    fn set_output_kind(&mut self, kind: LinkOutputKind) {
        todo!()
    }

    fn set_output_filename(&mut self, filename: &Path) {
        todo!()
    }

    fn link_dylib(&mut self, lib: &str, verbatim: bool, as_needed: bool) {
        todo!()
    }

    fn link_static_lib(&mut self, lib: &str, verbatim: bool) {
        todo!()
    }

    fn include_path(&mut self, path: &Path) {
        todo!()
    }

    fn add_object(&mut self, path: &Path) {
        todo!()
    }

    fn optimize(&mut self) {
        todo!()
    }

    fn gc_sections(&mut self) {
        todo!()
    }
}
