//! Hash Compiler token keyword definitions.
use core::ffi::c_size_t;
use std::{ffi::c_char, fmt};

use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use strum_macros::AsRefStr;

/// Enum Variants for keywords.
#[derive(Debug, Copy, Clone, PartialEq, Eq, AsRefStr, FromPrimitive)]
#[strum(serialize_all = "snake_case")]
#[repr(u8)]
pub enum Keyword {
    For,
    While,
    Loop,
    If,
    Else,
    Match,
    As,
    In,
    Trait,
    Enum,
    Struct,
    Continue,
    Break,
    Return,
    Import,
    Raw,
    False,
    Unsafe,
    Pub,
    Priv,
    Mut,
    Mod,
    Impl,
    True,
    Type,
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}

#[repr(C)]
struct Kw {
    keyword: *const c_char,
    num: u8,
}

extern "C" {
    fn is_hash_keyword(str: *const c_char, len: c_size_t) -> *mut Kw;
}

pub fn ident_is_keyword(str: &str) -> Option<Keyword> {
    // If the length of string is greater than 8, not a keyword.
    if str.len() > 8 {
        return None;
    }

    // Create a stack buffer of 9bytes, and copy the buffer
    let mut buf = [0u8; 9];
    buf[..str.len()].copy_from_slice(str.as_bytes());

    let kw = unsafe {
        // convert str into c str
        is_hash_keyword(buf.as_ptr() as *const i8, str.len())
    };

    if kw.is_null() {
        None
    } else {
        Keyword::from_u8(unsafe { (*kw).num })
    }
}
