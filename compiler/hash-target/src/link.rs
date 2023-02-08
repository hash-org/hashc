//! Definitions and data types that characterise linking
//! variants for platforms.
//!
//! Ideally, this would live in `hash-link`, but this would create
//! a circular dependency between `hash-link` and `hash-target`, so...

use std::{borrow::Cow, collections::BTreeMap};

/// Linker is called through a C/C++ compiler.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Cc {
    Yes,
    No,
}

/// Linker is LLD.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Lld {
    Yes,
    No,
}

/// Linker flavour, determines which linker is used to for
/// which target.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum LinkerFlavour {
    /// GNU linker for Linux and other Unix-like targets.
    Gnu(Cc, Lld),

    /// Unix-like linker for Apple targets.
    Darwin(Cc, Lld),

    /// MSVC Linker for Windows and UEFI.
    Msvc(Lld),
}

#[derive(Debug, Clone, Copy)]
pub enum FramePointer {
    /// Always preserve the function frame pointer.
    AlwaysPreserve,

    /// Allow for the frame pointer to be disregarded for
    /// leaf functions, i.e. functions that never call any
    /// other functions.
    Leaf,

    /// No particular restrictions on the frame pointer, it is up
    /// to the linker to decide what to do.
    None,
}

#[derive(Debug, Clone, Copy)]
pub enum CodeModel {
    /// The default code model.
    Default,

    /// The JIT code model.
    JITDefault,

    /// The small code model.
    Small,

    /// The kernel code model.
    Kernel,

    /// The medium code model.
    Medium,

    /// The large code model.
    Large,
}

#[derive(Debug, Clone, Copy)]
pub enum RelocationMode {
    /// The default relocation mode.
    Default,

    /// The static relocation mode.
    Static,

    /// The PIC relocation mode.
    PIC,

    /// The dynamic no PIC relocation mode.
    DynamicNoPIC,
}

/// A collection of linker arguments that are applied to the
/// linker invocation provided that the correct platform is
/// specified.
#[derive(Debug, Clone, Default)]
pub struct LinkageArgs {
    args: BTreeMap<LinkerFlavour, Vec<Cow<'static, str>>>,
}

impl LinkageArgs {
    /// Create a new empty collection of linker arguments.
    pub fn new() -> Self {
        Self { args: BTreeMap::new() }
    }

    /// Add a collection of arguments to the [LinkageArgs] for the
    /// given [LinkerFlavour].
    pub fn add_args(
        &mut self,
        flavour: LinkerFlavour,
        args: impl Iterator<Item = Cow<'static, str>> + Clone,
    ) {
        let mut insert = |flavour| self.args.entry(flavour).or_default().extend(args.clone());
        insert(flavour);

        match flavour {
            LinkerFlavour::Gnu(cc, lld) => {
                debug_assert_eq!(lld, Lld::No); // It can't not be if we're adding args.

                insert(LinkerFlavour::Gnu(cc, Lld::Yes));
            }
            LinkerFlavour::Darwin(cc, lld) => {
                debug_assert_eq!(lld, Lld::No); // It can't not be if we're adding args.

                insert(LinkerFlavour::Darwin(cc, Lld::Yes));
            }
            LinkerFlavour::Msvc(lld) => {
                debug_assert_eq!(lld, Lld::No); // It can't not be if we're adding args.

                insert(LinkerFlavour::Msvc(Lld::Yes));
            }
        }
    }

    /// Add link arguments to the given [LinkerFlavour] that are [str]s.
    pub fn add_str_args(&mut self, flavour: LinkerFlavour, args: &[&'static str]) {
        self.add_args(flavour, args.iter().copied().map(Cow::Borrowed))
    }
}

/// A collection of linker environment variables that are applied to the
/// linker invocation provided that the correct platform is specified.
pub type LinkEnv = Cow<'static, [Cow<'static, str>]>;

pub macro link_env {
    () => {
        Cow::Borrowed(&[])
    },
    ($($variable: expr),+ $(,)?) => {
        Cow::Borrowed(&[
            $(
                Cow::Borrowed($variable),
            )*
        ])
    }
}
