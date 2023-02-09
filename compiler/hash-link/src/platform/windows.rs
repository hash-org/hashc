//! Windows specific linker configuration and option utilities.

use cc::Tool;

/// Function that uses the Windows registry to find the required linker.
pub(crate) fn find_tool(target_triple: &str, tool: &str) -> Option<Tool> {
    cc::windows_registry::find_tool(target_triple, tool)
}

/// Function to check whether Visual Studio is installed on the
/// system.
pub(crate) fn is_vs_installed() -> bool {
    cc::windows_registry::find_vs_version().is_ok()
}
