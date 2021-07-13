//! File describing all the variants of Tokens that can be present within a 
//! Hash source file.
//!
//! All rights reserved 2021 (c) The Hash Language authors

pub enum Token {
    Eq,
    Neq,
    Assign,
    Not,
    LogicalAnd,
    LogicalOr,
    Plus,
    Minus,
    Asterisk, // Named like so since it is used in various contexts
    Ampersand,
    Exp, // ^^
    Div,
    Modulo,
    RightBitShift,
    LeftBitShift,
    BitNot,
    BitXor, // ^

    Pipe, // |
    // Arrow, // ->
    ThickArrow, // =>

    // Keywords
    Let,
    As,
    Struct,
    Enum,
    Trait,
    Where,
    Import,
    Loop,
    While,
    For,
    In,
    If,
    Else,
    Match,
    Break,
    Continue,
    Return,

    // Parenthesees
    OpenCurly,
    CloseCurly,
    OpenParen,
    CloseParen,
    OpenSquare,
    CloseSquare,
    OpenAngle,
    CloseAngle,
}
