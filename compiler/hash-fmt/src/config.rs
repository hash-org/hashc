//! Contains all of the logic and data structures relating to configuring the
//! behaviour of the formatting.

/// All configuration details for printing the AST, i.e. information about
/// how much indentation to use, adding semi colons, respecting spans, etc.
#[derive(Debug, Clone, Copy)]
pub struct AstPrintingConfig {
    /// The number of spaces to use when indenting various AST constructs.
    pub indentation: u32,

    /// The maximum allowed width of a line, until the formatting attempts to
    /// wrap a line to the next line.
    pub max_width: u32,
}
