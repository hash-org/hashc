//! A stream interface for the compiler to write information to. This wrapper
//! is primarily used to abstract the notion of the compiler emitting messages
//! and information. In practise, this is used by some of the following items:
//!
//! - The [CompilerOutputStream] for the "test" compiler is wrapped in such a
//!   way that it can capture both `stdout` and `stderr` output.
//!
//! - It might be potentially used in the future with the meta-program to send
//!   and receive messages from the compiler.

use std::sync::{Arc, Mutex};

/// A [CompilerOutputStream] is used to specify where the output of the compiler
/// should be written to. This is used by the [CompilerInterface] to provide
/// the pipeline with the necessary information to write to the correct stream.
#[derive(Debug)]
pub enum CompilerOutputStream {
    /// A [CompilerOutputStream] that points to the `stdout` stream.
    Stdout(std::io::Stdout),

    /// A [CompilerOutputStream] that points to the `stderr` stream.
    Stderr(std::io::Stderr),

    /// A [CompilerOutputStream] that is backed by a [Mutex] and a [Vec].
    Owned(Arc<Mutex<Vec<u8>>>),
}

impl CompilerOutputStream {
    /// Create a new [CompilerOutputStream] which uses "stdout" as the output
    /// stream.
    pub fn stdout() -> Self {
        CompilerOutputStream::Stdout(std::io::stdout())
    }

    /// Create a new [CompilerOutputStream] which uses "stderr" as the output
    /// stream.
    pub fn stderr() -> Self {
        CompilerOutputStream::Stderr(std::io::stderr())
    }

    /// Create an owned [CompilerOutputStream].
    pub fn owned() -> Self {
        CompilerOutputStream::Owned(Arc::new(Mutex::new(Vec::new())))
    }
}

impl Clone for CompilerOutputStream {
    fn clone(&self) -> Self {
        match self {
            CompilerOutputStream::Stdout(_) => CompilerOutputStream::Stdout(std::io::stdout()),
            CompilerOutputStream::Stderr(_) => CompilerOutputStream::Stderr(std::io::stderr()),
            CompilerOutputStream::Owned(stream) => CompilerOutputStream::Owned(stream.clone()),
        }
    }
}

impl std::io::Write for CompilerOutputStream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match self {
            CompilerOutputStream::Stdout(stream) => stream.write(buf),
            CompilerOutputStream::Stderr(stream) => stream.write(buf),
            CompilerOutputStream::Owned(stream) => {
                let mut stream = stream.lock().unwrap();
                stream.extend_from_slice(buf);
                Ok(buf.len())
            }
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        match self {
            CompilerOutputStream::Stdout(stream) => stream.flush(),
            CompilerOutputStream::Stderr(stream) => stream.flush(),
            CompilerOutputStream::Owned(_) => Ok(()),
        }
    }
}
