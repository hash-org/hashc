//! For M1 & M2 folks.

use crate::{
    targets::apple_base::{self, AppleArch},
    Target,
};

/// Create a new [Target] for the `aarch64-apple-darwin` target.
pub fn target() -> Target {
    let apple_arch = AppleArch::Arm64;
    let mut base = apple_base::options_from("macos", apple_arch);
    base.cpu = "apple-a14".into();

    Target {
        name: apple_arch.llvm_target().into(),
        arch: apple_arch.into(),
        data_layout: "e-m:o-i64:64-i128:128-n32:64-S128".into(),
        pointer_bit_width: 64,
        ..base
    }
}
