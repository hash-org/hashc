//! Definitions to describe the target of Hash compilation.

pub mod abi;
pub mod alignment;
pub mod data_layout;
pub mod primitives;
pub mod size;

use std::{
    borrow::Cow,
    env::consts::ARCH,
    fmt::{Display, Formatter},
};

use abi::Abi;

/// The target that the compiler should compile for.
#[derive(Debug, Clone)]
pub struct Target {
    /// The size of the pointer for the target in bytes.
    ///
    /// N.B. It is an invariant for the pointer size to be
    /// larger than 8, there is no current host system that
    /// supports a pointer size larger than 8 bytes.
    pub pointer_width: usize,

    /// The target-triple name of the [Target].
    pub name: Cow<'static, str>,

    /// The architecture of the target.
    pub arch: TargetArch,

    /// The name of the entry point for the target.
    ///
    /// Default is `main`.
    pub entry_name: Cow<'static, str>,

    /// Specifies the name of the cpu that the target has.
    pub cpu: Cow<'static, str>,

    /// This specifies the CPU features that are available on the
    /// target that is being compiled for.
    pub cpu_features: Cow<'static, str>,

    /// Represents what kind of relocation model the target is
    /// expecting.
    pub relocation_mode: RelocationMode,

    /// Represents what kind of code model the target is expecting.
    pub code_model: CodeModel,

    /// The integer width of the target in bits.
    pub c_int_width: u8,

    /// The default visibility for symbols in this target should be "hidden"
    /// rather than "default"
    pub default_hidden_visibility: bool,

    /// If the entry point of the program requires that the program arguments
    /// are passed in the form of `int main(int argc, char** argv)`.
    pub entry_point_requires_args: bool,

    /// The ABI of the entry function, the default is
    /// the `C` ABI.
    pub entry_abi: Abi,
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

/// Represents the available target architectures that the compiler can compiler
/// for.
#[derive(Debug, Clone, Copy)]
pub enum TargetArch {
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

impl TargetArch {
    /// Get the [TargetArch] from the host system.
    pub fn from_host() -> Self {
        match ARCH {
            "x86" => Self::X86,
            "x86_64" | "x86-64" | "x64" => Self::X86_64,
            "aarch64" => Self::Aarch64,
            "arm" => Self::Arm,
            _ => Self::Unknown,
        }
    }

    /// Convert the [TargetName] to a static string.
    pub fn as_str(&self) -> &'static str {
        match self {
            TargetArch::X86 => "x86",
            TargetArch::X86_64 => "x86-64",
            TargetArch::Aarch64 => "aarch64",
            TargetArch::Arm => "arm",
            TargetArch::Unknown => "unknown",
        }
    }
}

impl Display for TargetArch {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TargetArch::X86 => write!(f, "x86"),
            TargetArch::X86_64 => write!(f, "x86_64"),
            TargetArch::Aarch64 => write!(f, "aarch64"),
            TargetArch::Arm => write!(f, "arm"),
            TargetArch::Unknown => write!(f, "unknown"),
        }
    }
}

impl Target {
    /// Create a new target from the given string.
    pub fn from_string(name: String) -> Option<Self> {
        // @@Todo: move each branch into separate module in order
        // to make it easier to add new targets.
        let (cpu, arch, pointer_width) = match name.as_str() {
            "x86" => ("x86-64", TargetArch::X86, 4),
            "x86_64" => ("x86-64", TargetArch::X86_64, 8),
            "arm" => ("arm", TargetArch::Arm, 4),
            "aarch64" => ("aarch64", TargetArch::Aarch64, 8),
            _ => return None,
        };

        Some(Self { cpu: cpu.into(), arch, pointer_width, ..Default::default() })
    }
}

impl Default for Target {
    fn default() -> Self {
        // get the size of the pointer for the current system
        let pointer_width = std::mem::size_of::<usize>();
        let arch = TargetArch::from_host();

        Self {
            name: env!("TARGET_TRIPLE").into(),
            c_int_width: 32,
            cpu: "generic".into(),
            cpu_features: "".into(),
            relocation_mode: RelocationMode::PIC,
            code_model: CodeModel::Default,
            pointer_width,
            arch,
            entry_name: "main".into(),
            entry_point_requires_args: true,
            entry_abi: Abi::C,
            default_hidden_visibility: false,
        }
    }
}

/// Holds information about various targets that are currently used by the
/// compiler.
#[derive(Debug, Clone, Default)]
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

    /// Update the target that the compiler is compiling for.
    pub fn set_target(&mut self, target: Target) {
        self.target = target;
    }
}
