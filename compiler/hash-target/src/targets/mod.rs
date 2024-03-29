//! Contains definitions and specific configuration per
//! compilation platform.

mod apple_base;
mod linux_base;
mod linux_gnu_base;
mod windows_msvc_base;

use crate::Target;

/// This macro registers all of the available compiler targets
/// based on the target triple.
macro_rules! register_targets {
    ( $(($triple:literal, $module: ident),)+ ) => {
        $(mod $module;)+

        pub const AVAILABLE_TARGETS: &[&str] = &[$($triple),+];

        pub(super) fn load_target(target: &str) -> Option<Target> {
            match target {
                $($triple => Some($module::target()),)+
                _ => None,
            }
        }
    }
}

register_targets! {
    ("x86_64-unknown-linux-gnu",x86_64_unknown_linux_gnu),
    ("x86_64-apple-darwin", x86_apple_darwin),
    ("aarch64-apple-darwin", aarch64_apple_darwin),
    ("x86_64-pc-windows-msvc", x86_64_pc_windows_msvc),
}
