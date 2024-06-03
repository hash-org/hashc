//! Utility for controlling and wrapping the output and error streams
//! that the compiler uses. This is useful for both running the compiler
//! in a "managed" environment, such as an LSP instance or a testing
//! environment - where both the output and error streams are captured
//! and can be queried for diagnostics.
