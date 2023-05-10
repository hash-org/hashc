//! Contains all of the logic and data structures relating to storing
//! the state of the formatting process.

/// Represents the state of the printer.
#[derive(Debug, Clone, Default)]
pub struct AstPrinterState {
    /// The current level of the indentation.
    pub indentation: u8,

    /// The current line width of the line, this is used to control whether the
    /// formatter should wrap the current line where it can or if it can
    /// continue to print some item on the current line.
    pub width: u16,

    /// The buffer that is used to store the result of the formatting
    /// temporarily until the entire file or AST node is ready to be printed.
    pub buffer: Vec<String>,
}
