//! Apple specific linker configuration and option utilities.

use std::{path::Path, process::Command};

use hash_pipeline::settings::CompilerSettings;
use hash_target::{
    link::{Cc, LinkerFlavour},
    HasTarget,
};

use crate::{error::LinkerError, linker::Linker};

/// This function adds the Apple SDK to the linker command which
/// is required for apple platforms.
///
/// N.B. This does not add the SDK if the target platform and architecture
/// is not Apple-like.
pub fn add_sdk<'a>(
    linker: &mut dyn Linker,
    flavour: LinkerFlavour,
    settings: &'a CompilerSettings,
) -> Result<(), LinkerError<'a>> {
    let target = settings.target();

    let arch = target.arch.as_str();
    let os = target.os.as_ref();
    let vendor = target.vendor.as_ref();

    if vendor != "apple"
        && !matches!(os, "macos")
        && !matches!(flavour, LinkerFlavour::Darwin(_, _))
    {
        return Ok(());
    }

    // This will be added by Lld itself...
    if os == "macos" && !matches!(flavour, LinkerFlavour::Darwin(Cc::No, _)) {
        return Ok(());
    }

    // Compute the SDK name based on the `arch`, `os`, and `target_name`.
    //
    // @@Future: apple has `tvos`, `ios`, `watchos`, which all have slightly
    // different sdk names, so we will have to handle these here in the future.
    let sdk_name = match (arch, os) {
        (_, "macos") => Ok("macosx"),
        _ => Err(LinkerError::UnsupportedArch { arch: target.arch, os: target.os.as_ref() }),
    }?;

    let sdk_root = get_apple_sdk_root(sdk_name)?;

    match flavour {
        LinkerFlavour::Darwin(Cc::Yes, _) => {
            linker.cmd().args(["-isysroot", &sdk_root, "-Wl,-syslibroot", &sdk_root]);
        }
        LinkerFlavour::Darwin(Cc::No, _) => {
            linker.cmd().args(["-syslibroot", &sdk_root]);
        }
        _ => unreachable!(),
    }

    Ok(())
}

/// Function that will find and compute the SDK root path for the MacOS
/// platform. This is defined from what Clang does:
///
/// <https://github.com/llvm/llvm-project/blob/6a63e21cf4e6a8499d90e2337eb545644646ee31/clang/lib/Driver/ToolChains/Darwin.cpp#L2080-L2100>
fn get_apple_sdk_root(sdk_name: &str) -> Result<String, LinkerError<'_>> {
    if let Ok(sdk_root) = std::env::var("SDKROOT") {
        let path = Path::new(&sdk_root);

        // Ignore `SDKROOT` if it's clearly set for the wrong platform.
        match sdk_name {
            "macosx10.15"
                if sdk_root.contains("iPhoneOS.platform")
                    || sdk_root.contains("iPhoneSimulator.platform") => {}
            _ if !path.is_absolute() || path == Path::new("/") || !path.exists() => {}
            _ => return Ok(sdk_root),
        };
    }

    // Now we fallback onto using `xcrun` to find the SDK root.
    let result =
        Command::new("xcrun").arg("--show-sdk-path").arg("-sdk").arg(sdk_name).output().and_then(
            |output| {
                if output.status.success() {
                    Ok(String::from_utf8(output.stdout).unwrap())
                } else {
                    Err(std::io::Error::other(String::from_utf8(output.stderr).unwrap()))
                }
            },
        );

    match result {
        Ok(output) => Ok(output.trim().to_string()),
        Err(error) => Err(LinkerError::AppleSdkRootError { name: sdk_name, error }),
    }
}
