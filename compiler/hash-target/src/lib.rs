//! Definitions to describe the target of Hash compilation.

pub mod abi;
pub mod alignment;
pub mod layout;
pub mod primitives;
pub mod size;

use std::{
    env::consts::ARCH,
    fmt::{Display, Formatter},
};

/// The target that the compiler should compile for.
#[derive(Debug, Clone, Copy)]
pub struct Target {
    /// The size of the pointer for the target in bytes.
    ///
    /// N.B. It is an invariant for the pointer size to be
    /// larger than 8, there is no current host system that
    /// supports a pointer size larger than 8 bytes.
    pub pointer_width: usize,

    /// The name of the target.
    pub name: TargetName,
}

/// Represents the available targets that the compiler can compiler for.
#[derive(Debug, Clone, Copy)]
pub enum TargetName {
    /// x86 32-bit target architecture.
    X86,

    /// x86 64-bit target architecture.
    X86_64,

    /// ARM 64-bit target architecture.
    Aarch64,

    /// ARM 32-bit target architecture.
    Arm,

    /// Used for when the target name is not known, but can
    /// still be compiled for.
    Unknown,
}

impl TargetName {
    pub fn from_system() -> Self {
        match ARCH {
            "x86" => Self::X86,
            "x86_64" => Self::X86_64,
            "aarch64" => Self::Aarch64,
            "arm" => Self::Arm,
            _ => Self::Unknown,
        }
    }
}

impl Display for TargetName {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TargetName::X86 => write!(f, "x86"),
            TargetName::X86_64 => write!(f, "x86_64"),
            TargetName::Aarch64 => write!(f, "aarch64"),
            TargetName::Arm => write!(f, "arm"),
            TargetName::Unknown => write!(f, "unknown"),
        }
    }
}

impl Target {
    /// Create a new target from the given name and pointer width.
    pub fn new(name: TargetName, pointer_width: usize) -> Self {
        Self { name, pointer_width }
    }

    /// Create a new target from the given string.
    pub fn from_string(name: String) -> Option<Self> {
        match name.as_str() {
            "x86" => Some(Self::new(TargetName::X86, 4)),
            "x86_64" => Some(Self::new(TargetName::X86_64, 8)),
            "arm" => Some(Self::new(TargetName::Arm, 4)),
            "aarch64" => Some(Self::new(TargetName::Aarch64, 8)),
            _ => None,
        }
    }
}

impl Default for Target {
    fn default() -> Self {
        // get the size of the pointer for the current system
        let pointer_width = std::mem::size_of::<usize>();
        let name = TargetName::from_system();

        Self { pointer_width, name }
    }
}

/// Holds information about various targets that are currently used by the
/// compiler.
#[derive(Debug, Clone, Copy, Default)]
pub struct TargetInfo {
    /// The target value of the host that the compiler is running
    /// for.
    host: Target,

    /// The target that the compiler is compiling for.
    target: Target,
}

impl TargetInfo {
    /// Create a new target info from the given host and target.
    pub fn new(host: Target, target: Target) -> Self {
        Self { host, target }
    }

    /// Get the target that the compiler is compiling for.
    pub fn target(&self) -> &Target {
        &self.target
    }

    /// Get the host target that the compiler is running on.
    pub fn host(&self) -> &Target {
        &self.host
    }
}
