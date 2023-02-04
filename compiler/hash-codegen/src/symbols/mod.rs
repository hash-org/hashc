//! Common utilities to aid code generation backends when creating symbol
//! names for items that are generated/emitted by the compiler.

pub mod mangle;

/// The maximum base that can be used for encoding numbers into strings.
pub const MAX_BASE: usize = 64;

/// The base used for alphanumeric symbols.
pub const ALPHANUMERIC_BASE: usize = 62;

/// The base used for case insensitive symbols.
pub const CASE_INSENSITIVE_BASE: usize = 36;

/// The alphabet used for encoding numbers into strings.
const BASE: &[u8] = b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ@$";

/// A utility function that is used to push a string representation of a
/// number into a string buffer. The number is encoded in the specified
/// `base` and the result is pushed into the `output` string buffer.
#[inline]
pub fn push_string_encoded_count(mut count: u128, base: usize, output: &mut String) {
    debug_assert!((2..=64).contains(&base));

    let mut buf = [0; 128];
    let mut i = buf.len();

    let base = base as u128;

    loop {
        i -= 1;
        buf[i] = BASE[(count % base) as usize];
        count /= base;

        if count == 0 {
            break;
        }
    }

    output.push_str(std::str::from_utf8(&buf[i..]).unwrap());
}
