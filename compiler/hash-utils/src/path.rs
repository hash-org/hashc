//! Path manipulation and canonicalisation utilities.

use std::{fs::canonicalize, path::Path};

/// Function to apply formatting onto a path when printing it.
#[cfg(not(target_os = "windows"))]
pub fn adjust_canonicalisation<P: AsRef<Path>>(p: P) -> String {
    canonicalize(p.as_ref()).unwrap_or_else(|_| p.as_ref().to_path_buf()).display().to_string()
}

/// Function to apply formatting onto a path when printing it.
#[cfg(target_os = "windows")]
pub fn adjust_canonicalisation<P: AsRef<Path>>(p: P) -> String {
    const VERBATIM_PREFIX: &str = r"\\?\";
    let path =
        canonicalize(p.as_ref()).unwrap_or_else(|_| p.as_ref().to_path_buf()).display().to_string();

    if let Some(stripped_path) = path.strip_prefix(VERBATIM_PREFIX) {
        stripped_path.to_string()
    } else {
        path
    }
}
