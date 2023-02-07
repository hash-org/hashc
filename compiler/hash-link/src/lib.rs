//! This crate contains all of the logic surrounding a linker
//! interface. This provides a generic [Linker] trait which is then
//! implemented by several linker flavours (e.g. `msvc` and `lld`)
#![allow(unused)]

pub mod gcc;
pub mod lld;
pub mod mold;
pub mod msvc;

use std::{path::Path, process::Command};

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
