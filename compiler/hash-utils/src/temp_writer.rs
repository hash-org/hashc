//! Utility for temporarily writing something to a buffer.
use std::io;

use derive_more::Constructor;

#[derive(Constructor, Default)]
pub struct TempWriter(Vec<u8>);

impl TempWriter {
    pub fn into_string(self) -> String {
        String::from_utf8(self.0).unwrap()
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
