//! This module is dedicated to encapsulating all logic related
//! to linking executables that includes "platform" specific linker
//! options.

use std::{io, path::Path, process::Output};

use crate::command::LinkCommand;

pub(crate) mod apple;
pub(crate) mod windows;

/// Disable localisation on all platforms by specifying the environment
/// variables on each system to disable localisation.
///
/// For unix-like systems, we set `LC_ALL` to `C` to disable localisation.
/// This is somewhat documented on <https://en.cppreference.com/w/cpp/locale/LC_categories>
///
/// For Windows VSBuild, we set the `VSLANG` environment variable to `1033` to
/// disable localisation. As per usual with Windows, this is undocumented.
pub fn disable_localisation(linker: &mut LinkCommand) {
    linker.env("LC_ALL", "C");
    linker.env("VSLANG", "1033");
}

/// This function is used to flush the created linker file to disk. For
/// non-Windows targets this does nothing since they always flush the produced
/// item into
#[cfg(not(windows))]
pub fn flush_linked_file(_: &io::Result<Output>, _: &Path) -> io::Result<()> {
    Ok(())
}

/// On Windows, under high I/O load, output buffers are sometimes not flushed,
/// even long after process exit, causing nasty, non-reproducible output bugs.
///
/// [`File::sync_all()`] calls `FlushFileBuffers()` down the line, which solves
/// the problem.
///
/// А full writeup of the original Chrome bug can be found at
/// <randomascii.wordpress.com/2018/02/25/
/// compiler-bug-linker-bug-windows-kernel-bug/amp>
#[cfg(windows)]
pub fn flush_linked_file(_: &io::Result<Output>, _: &Path) -> io::Result<()> {
    todo!()
}

/// Check if the attempted execution of a [Command] resulted in the host
/// operating system complaining that the spawn limit was exceeded.
#[cfg(unix)]
pub fn command_line_too_big(err: &io::Error) -> bool {
    err.raw_os_error() == Some(::libc::E2BIG)
}

#[cfg(windows)]
pub fn command_line_too_big(err: &io::Error) -> bool {
    const ERROR_FILENAME_EXCED_RANGE: i32 = 206;
    err.raw_os_error() == Some(ERROR_FILENAME_EXCED_RANGE)
}

#[cfg(not(any(unix, windows)))]
pub fn command_line_too_big(_: &io::Error) -> bool {
    false
}
