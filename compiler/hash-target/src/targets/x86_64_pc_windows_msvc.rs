//! Target specifications for the x86_64-pc-windows-msvc target.

use super::windows_msvc_base;
use crate::{Target, TargetArch};

pub fn target() -> Target {
    let mut base = windows_msvc_base::options();
    base.cpu = "x86-64".into();

    Target {
        name: "x86_64-pc-windows-msvc".into(),
        pointer_bit_width: 64,
        data_layout: "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
            .into(),
        arch: TargetArch::X86_64,
        ..base
    }
}
