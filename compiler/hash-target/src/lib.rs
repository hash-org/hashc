//! Definitions to describe the target of Hash compilation.
#![feature(decl_macro)]

pub mod abi;
pub mod alignment;
pub mod data_layout;
pub mod discriminant;
pub mod link;
pub mod primitives;
pub mod size;
pub mod targets;

use std::{
    borrow::Cow,
    env::consts::{ARCH, OS},
    fmt::{self, Display, Formatter},
};

use abi::{Abi, Integer};
use data_layout::{Endian, TargetDataLayout, TargetDataLayoutParseError};
use link::{
    link_env, Cc, CodeModel, FramePointer, LinkEnv, LinkageArgs, LinkerFlavour, Lld,
    RelocationModel,
};
use size::Size;
use targets::load_target;

/// The host target that the compiler is currently running on.
pub const HOST_TARGET_TRIPLE: &str = env!("TARGET_TRIPLE");

/// Represents all of the available compilation platforms that
/// the compiler can compiler for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Platform {
    /// The platform is unknown.
    Unknown,

    /// The platform is Linux like.
    Linux,

    /// The platform is Windows like.
    Windows,

    /// The platform is MacOS/iOS like.
    OsX,
}

impl Platform {
    /// Check if the platform is like "Windows".
    pub fn is_windows(self) -> bool {
        matches!(self, Platform::Windows)
    }
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

/// The target that the compiler should compile for.
#[derive(Debug, Clone)]
pub struct Target {
    /// The size of the pointer for the target in bits.
    ///
    /// N.B. It is an invariant for the pointer size to be
    /// larger than 8, there is no current host system that
    /// supports a pointer size larger than 8 bits.
    pub pointer_bit_width: usize,

    /// The string name of the operating system that the target
    /// is for. If the name is "", this means that the target
    /// OS is not known.
    pub os: Cow<'static, str>,

    /// If the target platform is either Windows, MacOS, Linux, or unknown.
    pub platform: Platform,

    /// The target-triple name of the [Target]. This is primarily
    /// needed for the LLVM backend to correctly configure the right
    /// target.
    pub name: Cow<'static, str>,

    /// The architecture of the target.
    pub arch: TargetArch,

    /// The data layout of the architecture.
    pub data_layout: Cow<'static, str>,

    /// The equivalent of `data_layout`, but parsed into a structural
    /// format.
    target_data_layout: TargetDataLayout,

    /// What endianess the target is.
    pub endian: Endian,

    /// The name of the entry point for the target.
    ///
    /// Default is `main`.
    pub entry_name: Cow<'static, str>,

    /// Specifies the name of the cpu that the target has.
    pub cpu: Cow<'static, str>,

    /// This specifies the CPU features that are available on the
    /// target that is being compiled for.
    pub cpu_features: Cow<'static, str>,

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

    /// The vendor name of the target.
    pub vendor: Cow<'static, str>,

    // ---- Linking stuff ----
    /// The linker flavour for the target.
    pub linker_flavour: LinkerFlavour,

    /// Represents what kind of relocation model the target is
    /// expecting.
    pub relocation_mode: RelocationModel,

    /// Represents what kind of code model the target is expecting.
    pub code_model: CodeModel,

    /// Represents what kind of frame pointer handling the target is expecting.
    pub frame_pointer: FramePointer,

    /// The suffix for dynamic libraries, e.g. `lib` on MacOS.
    pub dylib_suffix: Cow<'static, str>,

    /// The prefix for dynamic libraries, e.g. `dylib` on MacOS.
    pub dylib_prefix: Cow<'static, str>,

    /// The prefix for static libraries, e.g. `lib` on Linux.
    pub staticlib_prefix: Cow<'static, str>,

    /// The suffix for static libraries, e.g. `lib` on Linux.
    pub staticlib_suffix: Cow<'static, str>,

    /// The suffix for executables, e.g. `exe` on Windows.
    pub exe_suffix: Cow<'static, str>,

    /// Whether dynamic linking is available on this target. Defaults to false.
    pub dynamic_linking: bool,

    /// Emit each function in its own section. Defaults to true.
    pub function_sections: bool,

    /// Whether the CRT can be linked statically or not.
    pub crt_statically_linked: bool,

    /// Arguments that are added to the linker at the beginning of the
    /// link line.
    pub pre_link_args: LinkageArgs,

    /// Arguments that are added to the linker at the end of the
    /// link line.
    pub post_link_args: LinkageArgs,

    /// Linker arguments that are unconditionally passed after any
    /// user-defined but before post-link objects. Standard platform
    /// libraries that should be always be linked to, usually go here.
    pub late_link_args: LinkageArgs,

    /// Environment variables that should be set when linking.
    pub link_env: Cow<'static, [(Cow<'static, str>, Cow<'static, str>)]>,

    /// Environment variables that should be removed when linking.
    pub link_env_remove: LinkEnv,
    // -----------------------
}

impl Target {
    /// Get the size of the pointer for the target in bits.
    pub fn ptr_size(&self) -> Size {
        Size::from_bits(self.pointer_bit_width as u64)
    }

    /// Adjust a given [ABI] to match the specifics of the
    /// target. Currently, we don't support any other ABI
    /// except "Hash", so this function will do nothing. However,
    /// when we support various other CPP ABIs like "stdcall", "fastcall",
    /// "vectorcall", etc, this function will be used to adjust the
    /// ABI to match the target details.
    pub fn adjust_abi(&self, abi: Abi) -> Abi {
        abi
    }

    /// Find and load the specified target from a target triple.
    ///
    /// @@Future: support a more custom way of loading in target specifications.
    pub fn search(triple: &str) -> Option<Self> {
        load_target(triple)
    }

    /// Get the [TargetDataLayout] that is associated with this [Target], if
    /// there exists one.
    ///
    /// @@Ugh: this is a shit API, we need to figure out how to unify a the
    /// target and target data layout items.
    pub fn data_layout(&self) -> &TargetDataLayout {
        &self.target_data_layout
    }

    /// Set the [TargetDataLayout] for the [Target].Ì
    pub fn set_data_layout(&mut self, dl: TargetDataLayout) {
        self.target_data_layout = dl;
    }

    /// Produce a [TargetDataLayout] from the given [Target] layout
    /// string. If the layout contains any errors, this function will
    /// return the errors that were encountered.
    pub fn parse_data_layout(&self) -> Result<TargetDataLayout, TargetDataLayoutParseError<'_>> {
        let mut dl = TargetDataLayout::parse_from_llvm_data_layout_string(&self.data_layout)?;

        // Check Endianness matches
        if dl.endian != self.endian {
            return Err(TargetDataLayoutParseError::InconsistentTargetArchitecture {
                dl: dl.endian.as_str(),
                target: self.endian.as_str(),
            });
        }

        // Check pointer sizes match
        let ptr_width: u64 = self.pointer_bit_width as u64;

        if dl.pointer_size.bits() != ptr_width {
            return Err(TargetDataLayoutParseError::InconsistentTargetPointerWidth {
                size: dl.pointer_size.bits(),
                target: ptr_width,
            });
        }

        // Apply the target c-enum size to the data layout since this is
        // not specified within the data layout string. If the size is larger
        // than the size of an integer, then we will return an error.
        dl.c_style_enum_min_size = match Integer::from_size(Size::from_bits(self.c_int_width)) {
            Some(bits) => bits,
            None => {
                return Err(TargetDataLayoutParseError::InvalidEnumSize {
                    err: format!("unsupported integer width `{}`, it must be defined as either `i8`, `i16`, `i32`, `i64`, or `i128`", self.c_int_width),
                })
            }
        };

        Ok(dl)
    }

    /// Check if the target is a macOS-like target.
    pub fn is_like_osx(&self) -> bool {
        self.platform == Platform::OsX
    }

    /// Check if the target is a Windows-like target.
    pub fn is_like_windows(&self) -> bool {
        self.platform == Platform::Windows
    }

    /// Add pre-linker arguments to the target.
    pub fn add_pre_link_args(&mut self, flavour: LinkerFlavour, args: &[&'static str]) {
        self.pre_link_args.add_str_args(flavour, args)
    }

    /// Add post-linker arguments to the target.
    pub fn add_post_link_args(&mut self, flavour: LinkerFlavour, args: &[&'static str]) {
        self.post_link_args.add_str_args(flavour, args)
    }
}

impl Default for Target {
    fn default() -> Self {
        // get the size of the pointer for the current system
        let pointer_bit_width = std::mem::size_of::<usize>() * 8;
        let arch = TargetArch::from_host();
        Self {
            arch,
            endian: Endian::Little,
            os: OS.into(),
            platform: Platform::Unknown,
            name: HOST_TARGET_TRIPLE.into(),
            vendor: "unknown".into(),
            cpu: "generic".into(),
            cpu_features: "".into(),

            // ABI related options
            c_int_width: 32,

            // This is the default data-layout string that is specified within
            // the LLVM IR Language reference, for any registered platform this
            // value will be overridden for the platform specific data layout
            // string.
            data_layout: "e-m:e-i64:64-f80:128-n8:16:32:64-S128".into(),
            target_data_layout: TargetDataLayout::default(),
            pointer_bit_width,

            // Entry point options
            entry_name: "main".into(),
            entry_abi: Abi::C,
            entry_point_requires_args: true,

            // Linking options for the platform.
            linker_flavour: LinkerFlavour::Gnu(Cc::Yes, Lld::No),

            code_model: CodeModel::Default,
            relocation_mode: RelocationModel::Pic,
            default_hidden_visibility: false,

            dylib_prefix: "lib".into(),
            dylib_suffix: "lib".into(),
            staticlib_suffix: "lib".into(),
            staticlib_prefix: "lib".into(),
            exe_suffix: "".into(),
            frame_pointer: FramePointer::None,
            dynamic_linking: false,
            function_sections: true,
            crt_statically_linked: false,

            pre_link_args: LinkageArgs::new(),
            late_link_args: LinkageArgs::new(),
            post_link_args: LinkageArgs::new(),
            link_env: link_env![],
            link_env_remove: link_env![],
        }
    }
}

impl fmt::Display for Target {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// Utility trait for types that want to query the current compilation
/// target.
pub trait HasTarget {
    fn target(&self) -> &Target;
}

impl HasTarget for Target {
    #[inline]
    fn target(&self) -> &Target {
        self
    }
}
