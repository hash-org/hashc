use crate::{Target, TargetArch, link::{Lld, Cc}};

use super::linux_gnu_base;

pub fn target() -> Target {
    let mut base = linux_gnu_base::options();
    base.cpu = "x86-64".into();

    let flavour = crate::link::LinkerFlavour::Gnu(Cc::Yes, Lld::No);
    base.add_pre_link_args(flavour, &["-m64"]);
    base.add_post_link_args(flavour, &["-lm"]);

    Target {
        name: "x86_64-unknown-linux-gnu".into(),
        pointer_bit_width: 64,
        data_layout: "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
            .into(),
        arch: TargetArch::X86_64,
        ..base
    }
}
