//! Utility for temporarily writing something to a buffer.
use core::fmt;
use std::io;

use derive_more::Constructor;

#[derive(Constructor, Default)]
pub struct TempWriter(Vec<u8>);

impl TempWriter {
    pub fn into_string(self) -> String {
        unsafe { String::from_utf8_unchecked(self.0) }
    }

    pub fn as_str(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(&self.0) }
    }
}

impl io::Write for TempWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl fmt::Display for TempWriter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
