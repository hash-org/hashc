//! Defines a structure used to represent the tokens that the
//! parser expected at some point during parsing. [ExpectedItem]
//! is represented using [`bitflags!`] in order to allow for encoding
//! multiple [ExpectedItem]s into a single [ExpectedItem] value.

use std::fmt;

use hash_token::{delimiter::Delimiter, TokenKind};
use hash_utils::{bitflags::bitflags, printing::SequenceDisplay};

bitflags! {
    /// Defines what expected items could be encountered in a given context.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct ExpectedItem: u32 {
        /// An identifier.
        const Ident = 1 << 1;

        /// A literal token.
        const Literal = 1 << 2;

        /// A minus token.
        const Minus = 1 << 3;

        /// A plus token
        const Plus = 1 << 4;

        /// A dot.
        const Dot = 1 << 6;

        /// An exclamation mark token.
        const Exclamation = 1 << 7;

        /// A pound token.
        const Pound = 1 << 8;

        /// An ampersand token.
        const Amp = 1 << 9;

        /// A comma token.
        const Comma = 1 << 10;

        /// A colon token.
        const Colon = 1 << 11;

        /// An equal sign token.
        const Eq = 1 << 12;

        /// A `<` delimiter
        const Lt = 1 << 13;

        /// A `>` delimiter
        const Gt = 1 << 14;

        /// Left parenthesis
        const LeftParen = 1 << 15;

        /// Right parenthesis
        const RightParen = 1 << 16;

        /// Left brace
        const LeftBrace = 1 << 17;

        /// Right brace
        const RightBrace = 1 << 18;

        /// Left bracket
        const LeftBracket = 1 << 19;

        /// Right bracket
        const RightBracket = 1 << 20;

        /// Thin arrow.
        const ThinArrow = 1 << 21;

        /// Fat arrow.
        const FatArrow = 1 << 22;

        /// An access `::`.
        const Access = 1 << 23;

        /// A `pub` keyword
        const PubKw = 1 << 24;

        /// A `priv` keyword
        const PrivKw = 1 << 25;

        /// A `mut` keyword
        const MutKw = 1 << 26;

        const Visibility = Self::PubKw.bits()
                         | Self::PrivKw.bits();

        /// Convenient grouping of `operator`.
        ///
        /// @@Incomplete: add all token operators.
        const Op = Self::Minus.bits()
                 | Self::Plus.bits()
                 | Self::Lt.bits()
                 | Self::Gt.bits()
                 | Self::Amp.bits();

        /// Convenient left-wise delimiter mask.
        const DelimLeft = Self::LeftParen.bits()
                        | Self::LeftBrace.bits()
                        | Self::LeftBracket.bits()
                        | Self::Lt.bits();

        /// Tokens that can start a type.
        const Type = ExpectedItem::Amp.bits()
                   | ExpectedItem::Ident.bits()
                   | ExpectedItem::DelimLeft.bits()
                   | ExpectedItem::Exclamation.bits()
                   | ExpectedItem::Pound.bits();

        /// Tokens that can start a pattern.
        const Pat = Self::Literal.bits()
                  | Self::Ident.bits()
                  | Self::LeftParen.bits()
                  | Self::LeftBracket.bits();
    }
}

impl fmt::Display for ExpectedItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut toks = vec![];

        for kind in self.iter() {
            match kind {
                ExpectedItem::Ident => toks.push("identifier"),
                ExpectedItem::Literal => toks.push("literal"),
                ExpectedItem::Comma => toks.push(","),
                ExpectedItem::Colon => toks.push(":"),
                ExpectedItem::Minus => toks.push("-"),
                ExpectedItem::Plus => toks.push("-"),
                ExpectedItem::Dot => toks.push("."),
                ExpectedItem::Eq => toks.push("="),
                ExpectedItem::Lt => toks.push("<"),
                ExpectedItem::Gt => toks.push(">"),
                ExpectedItem::Amp => toks.push("&"),
                ExpectedItem::Exclamation => toks.push("!"),
                ExpectedItem::Pound => toks.push("#"),
                ExpectedItem::LeftParen => toks.push("("),
                ExpectedItem::RightParen => toks.push(")"),
                ExpectedItem::LeftBrace => toks.push("{"),
                ExpectedItem::RightBrace => toks.push("}"),
                ExpectedItem::LeftBracket => toks.push("["),
                ExpectedItem::RightBracket => toks.push("]"),
                ExpectedItem::ThinArrow => toks.push("->"),
                ExpectedItem::FatArrow => toks.push("=>"),
                ExpectedItem::Access => toks.push("::"),
                _ => unreachable!(),
            }
        }

        write!(f, "{}", SequenceDisplay::either(&toks))
    }
}

impl From<TokenKind> for ExpectedItem {
    fn from(value: TokenKind) -> Self {
        match value {
            TokenKind::Eq => ExpectedItem::Eq,
            TokenKind::Lt => ExpectedItem::Lt,
            TokenKind::Gt => ExpectedItem::Gt,
            TokenKind::Minus => ExpectedItem::Minus,
            TokenKind::Plus => ExpectedItem::Plus,
            TokenKind::Dot => ExpectedItem::Dot,
            TokenKind::Exclamation => ExpectedItem::Exclamation,
            TokenKind::Pound => ExpectedItem::Pound,
            TokenKind::Amp => ExpectedItem::Amp,
            TokenKind::Colon => ExpectedItem::Colon,
            TokenKind::Comma => ExpectedItem::Comma,
            TokenKind::Ident(_) => ExpectedItem::Ident,
            TokenKind::ThinArrow => ExpectedItem::ThinArrow,
            TokenKind::FatArrow => ExpectedItem::FatArrow,
            TokenKind::Access => ExpectedItem::Access,
            TokenKind::Tree(delim, _) | TokenKind::RightDelim(delim) => delim.into(),
            _ => unreachable!("unexpected token kind when deriving expected item: {:?}", value),
        }
    }
}

impl From<Delimiter> for ExpectedItem {
    fn from(value: Delimiter) -> Self {
        match value {
            Delimiter::Paren => ExpectedItem::LeftParen,
            Delimiter::Bracket => ExpectedItem::RightBracket,
            Delimiter::Brace => ExpectedItem::RightBracket,
            Delimiter::Angle => ExpectedItem::Gt,
        }
    }
}
