//! Target specifications for the x86_64-apple-darwin target.

use crate::{
    link::{Cc, FramePointer, LinkerFlavour, Lld},
    targets::apple_base::{self, AppleArch},
    Target,
};

/// Create a new [Target] for the `x86_64-apple-darwin` target.
pub fn target() -> Target {
    let apple_arch = AppleArch::X86_64;
    let mut base = apple_base::options_from("macos", apple_arch);

    base.frame_pointer = FramePointer::AlwaysPreserve;
    base.add_pre_link_args(LinkerFlavour::Darwin(Cc::Yes, Lld::No), &["-m64"]);

    Target {
        name: apple_arch.llvm_target().into(),
        arch: apple_arch.into(),
        pointer_bit_width: 64,
        data_layout: "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
            .into(),
        ..base
    }
}
