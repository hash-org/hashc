//! Base Apple architecture configurations.

use std::borrow::Cow;

use crate::{
    link::{Cc, FramePointer, LinkageArgs, LinkerFlavour, Lld},
    Platform, Target, TargetArch,
};

/// All of the architectures that Apple supports, and or has
/// machines that are of that architecture. This is only a subset
/// of the architectures that are available, however we only
/// support these architectures for now.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AppleArch {
    /// For x86_64 folks.
    X86_64,

    /// M1 & M2 folks.
    Arm64,
}

impl AppleArch {
    /// Get the architecture target CPU name.
    pub fn target_cpu(&self) -> &'static str {
        match self {
            AppleArch::X86_64 => "core2",
            AppleArch::Arm64 => "apple-a12",
        }
    }

    /// Get the target architecture name.
    pub fn target_name(&self) -> &'static str {
        match self {
            AppleArch::X86_64 => "x86_64",
            AppleArch::Arm64 => "arm64",
        }
    }

    /// Get the specific LLVM target for the particular architecture.
    pub fn llvm_target(&self) -> String {
        let (major, minor) = self.macos_deployment_target();
        format!("{}-apple-macosx{}.{}.0", self.target_name(), major, minor)
    }

    /// Get a major and minor version for the macOS deployment target.
    pub fn macos_deployment_target(&self) -> (u32, u32) {
        match self {
            AppleArch::X86_64 => (10, 7),
            AppleArch::Arm64 => (11, 0), // Lesser versions than 11.0 are not supported.
        }
    }

    /// Get the macOS platform version for the given architecture.
    pub fn platform_version(&self) -> String {
        let (major, minor) = self.macos_deployment_target();
        format!("{major}.{minor}")
    }
}

impl From<AppleArch> for TargetArch {
    fn from(arch: AppleArch) -> Self {
        match arch {
            AppleArch::X86_64 => Self::X86_64,
            AppleArch::Arm64 => Self::Aarch64,
        }
    }
}

/// Compute the pre-linking arguments the given [AppleArch]
/// with specific os and ABI.
pub fn compute_pre_link_args(os: &'static str, arch: AppleArch, _abi: &'static str) -> LinkageArgs {
    let version: Cow<'static, str> = arch.platform_version().into();
    let arch = arch.target_name();

    let mut args = LinkageArgs::new();

    // We just specify the architecture and the platform version
    // which is required for the darwin family linkers
    args.add_str_args(
        LinkerFlavour::Darwin(Cc::No, Lld::No),
        &["-arch", arch, "-platform_version", os],
    );
    args.add_args(LinkerFlavour::Darwin(Cc::No, Lld::No), [version.clone(), version].into_iter());

    args
}

/// Create a base [Target] for the given [AppleArch] and os. This
/// configures the [Target] with default values for any given Apple
/// platform target, any specific options are then later overridden
/// by `x86_64-apple-darwin` and `aarch64-apple-darwin`, etc.
pub fn options_from(os: &'static str, arch: AppleArch) -> Target {
    Target {
        cpu: arch.target_cpu().into(),
        arch: arch.into(),
        data_layout: "".into(),
        pointer_bit_width: 64,

        // Specify the DLL suffix for the target, it is always "dylib" for apple
        // targets.
        dylib_suffix: ".dylib".into(),
        vendor: "apple".into(),
        os: os.into(),
        platform: Platform::OsX,

        // macOS has -dead_strip, which doesn't rely on function_sections
        linker_flavour: LinkerFlavour::Darwin(Cc::Yes, Lld::No),
        dynamic_linking: true,
        function_sections: false,
        frame_pointer: FramePointer::AlwaysPreserve,

        pre_link_args: compute_pre_link_args(os, arch, ""),

        ..Default::default()
    }
}
