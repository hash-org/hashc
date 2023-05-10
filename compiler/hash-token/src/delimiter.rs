//! Hash Compiler token delimiter definitions.

/// A [Delimiter] is a [super::TokenKind] is used to denote a separation or a
/// nested token tree. The [Delimiter] does not contain the `<...>` because this
/// conflicts with the binary operators '<' and '>'.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Delimiter {
    /// Parenthesis, `(` or `)`
    Paren,
    /// Brace, `{` or `}`
    Brace,
    /// Bracket, `[` or `]`
    Bracket,
    /// Angle bracket, `<` or `>`
    Angle,
}

impl Delimiter {
    pub fn from_left(ch: char) -> Option<Delimiter> {
        match ch {
            '(' => Some(Delimiter::Paren),
            '[' => Some(Delimiter::Bracket),
            '{' => Some(Delimiter::Brace),
            '<' => Some(Delimiter::Angle),
            _ => None,
        }
    }

    pub fn from_right(ch: char) -> Option<Delimiter> {
        match ch {
            ')' => Some(Delimiter::Paren),
            ']' => Some(Delimiter::Bracket),
            '}' => Some(Delimiter::Brace),
            '>' => Some(Delimiter::Angle),
            _ => None,
        }
    }

    /// Get the left-hand side variant of a corresponding delimiter
    pub fn left(&self) -> char {
        match self {
            Delimiter::Paren => '(',
            Delimiter::Bracket => '[',
            Delimiter::Brace => '{',
            Delimiter::Angle => '<',
        }
    }

    /// Get the right-hand side variant of a corresponding delimiter
    pub fn right(&self) -> char {
        match self {
            Delimiter::Paren => ')',
            Delimiter::Bracket => ']',
            Delimiter::Brace => '}',
            Delimiter::Angle => '>',
        }
    }
}

/// Denotes which variant of the delimiter, either being left or right.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum DelimiterVariant {
    Left,
    Right,
}

impl std::fmt::Display for Delimiter {
    /// Display implementation for [Delimiter], it's always assumed that it's
    /// asking for the right hand-side variant of the delimiter.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.right())
    }
}
