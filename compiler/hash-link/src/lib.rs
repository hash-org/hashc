//! This crate contains all of the logic surrounding a linker
//! interface. This provides a generic [Linker] trait which is then
//! implemented by several linker flavours (e.g. `msvc` and `lld`)

use std::{path::Path, process::Command};

/// Everything is flattened to a single enum to make the json encoding/decoding
/// less annoying.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum LinkOutputKind {
    /// Dynamically linked non position-independent executable.
    DynamicNoPicExe,

    /// Dynamically linked position-independent executable.
    DynamicPicExe,

    /// Statically linked non position-independent executable.
    StaticNoPicExe,

    /// Statically linked position-independent executable.
    StaticPicExe,

    /// Regular dynamic library ("dynamically linked").
    DynamicDylib,

    /// Dynamic library with bundled libc ("statically linked").
    StaticDylib,
}

/// A trait which represents a linker and all of the functionality
/// that a linker should have.
pub trait Linker {
    /// Convert the current linker into a [Command] which can be executed.
    fn cmd(&mut self) -> &mut Command;

    /// Specify what the linker should output.
    fn set_output_kind(&mut self, output_kind: LinkOutputKind, out_filename: &Path);

    fn link_dylib(&mut self, lib: &str, verbatim: bool, as_needed: bool);

    fn include_path(&mut self, path: &Path);
}
