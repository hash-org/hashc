//! File describing all the variants of Tokens that can be present within a
//! Hash source file.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::fmt;

use crate::caching::{StringIdentifier, STRING_LITERAL_MAP};
use hash_ast::ident::Identifier;
use hash_ast::ident::IDENTIFIER_MAP;
use hash_ast::keyword::Keyword;
use hash_ast::location::Location;

pub type TokenResult<T> = Result<T, TokenError>;

/// A Lexeme token that represents the smallest code unit of a hash source file. The
/// token contains a kind which is elaborated by [TokenKind] and a [Location] in the
/// source that is represented as a span. The span is the beginning byte offset, and the
/// number of bytes for the said token.
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Location,
}

impl Token {
    pub fn new(kind: TokenKind, span: Location) -> Self {
        Token { kind, span }
    }

    pub fn has_kind(&self, right: TokenKind) -> bool {
        self.kind == right
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TokenKind::Ident(ident) => write!(f, "Ident ({})", IDENTIFIER_MAP.ident_name(*ident)),
            TokenKind::Tree(delim, tree) => {
                writeln!(f, "Delimiter({})", delim.left())?;

                for token in tree {
                    writeln!(f, "{}", token)?;
                }

                write!(f, "Delimiter({})", delim.right())
            }
            TokenKind::StrLiteral(literal) => {
                write!(
                    f,
                    "StringLiteral (\"{}\")",
                    STRING_LITERAL_MAP.lookup(*literal)
                )
            }
            // We want to print the actual character, instead of a potential escape code
            TokenKind::CharLiteral(ch) => {
                write!(f, "CharLiteral ('{}')", ch)
            }
            kind => write!(f, "{:?}", kind),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq)]
pub enum Delimiter {
    /// '(' or ')'
    Paren,
    /// '{' or '}'
    Brace,
    /// '[' or ']'
    Bracket,
}

impl Delimiter {
    pub fn from_left(ch: char) -> Option<Delimiter> {
        match ch {
            '(' => Some(Delimiter::Paren),
            '[' => Some(Delimiter::Bracket),
            '{' => Some(Delimiter::Brace),
            _ => None,
        }
    }

    /// Get the left-hand side variant of a corresponding delimiter
    pub fn left(&self) -> char {
        match self {
            Delimiter::Paren => '(',
            Delimiter::Bracket => '[',
            Delimiter::Brace => '{',
        }
    }

    /// Get the right-hand side variant of a corresponding delimiter
    pub fn right(&self) -> char {
        match self {
            Delimiter::Paren => ')',
            Delimiter::Bracket => ']',
            Delimiter::Brace => '}',
        }
    }
}

/// A TokenKind represents all variants of a token that can be present in a source file. Must of the
/// kinds only represents a single character, but some tokens account for an entire literal or an identifier.
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    /// '='
    Eq,
    /// '<'
    Lt,
    /// '>'
    Gt,
    /// '+'
    Plus,
    /// '-'
    Minus,
    /// '*'
    Star,
    /// '/'
    Slash,
    /// '%'
    Percent,
    /// '^'
    Caret,
    /// '&'
    Amp,
    /// '~'
    Tilde,
    /// '|'
    Pipe,
    /// '?'
    Question,
    /// '!'
    Exclamation,
    /// '.'
    Dot,
    /// ':'
    Colon,
    /// ';'
    Semi,
    /// '#'
    Hash,
    /// ','
    Comma,
    /// '"'
    Quote,
    /// "'"
    SingleQuote,
    /// Integer Literal
    IntLiteral(u64),
    /// Float literal
    FloatLiteral(f64),
    /// Character literal
    CharLiteral(char),
    /// StrLiteral,
    StrLiteral(StringIdentifier),
    /// Keyword
    Keyword(Keyword),
    /// Identifier
    Ident(Identifier),

    /// Delimiter: '(' '{', '[' and right hand-side variants, useful for error reporting and messages
    Delimiter(Delimiter, bool),

    /// A token tree is represented by an arbitrary number of tokens that are surrounded by
    /// a given delimiter kind, the variants are specified in the [Delimiter] enum.
    Tree(Delimiter, Vec<Token>),

    /// When the lexer hits an unexpected character, just label it as unexpected rather
    /// than declaring it as an immediate error
    Unexpected(char),
}

impl TokenKind {
    /// Check if a [TokenKind] can be considered in a situation as a unary operator.
    pub(crate) fn is_unary_op(&self) -> bool {
        matches!(
            self,
            TokenKind::Plus
                | TokenKind::Minus
                | TokenKind::Star
                | TokenKind::Slash
                | TokenKind::Amp
                | TokenKind::Tilde
                | TokenKind::Exclamation
        )
    }

    /// Check if the [TokenKind] is a primitive literal; either a 'char', 'int', 'float' or a 'string'
    pub(crate) fn is_literal(&self) -> bool {
        matches!(
            self,
            TokenKind::IntLiteral(_)
                | TokenKind::FloatLiteral(_)
                | TokenKind::CharLiteral(_)
                | TokenKind::StrLiteral(_)
        )
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Eq => write!(f, "="),
            TokenKind::Lt => write!(f, ">"),
            TokenKind::Gt => write!(f, ">"),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Star => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::Percent => write!(f, "%"),
            TokenKind::Caret => write!(f, "^"),
            TokenKind::Amp => write!(f, "&"),
            TokenKind::Tilde => write!(f, "~"),
            TokenKind::Pipe => write!(f, "|"),
            TokenKind::Question => write!(f, "?"),
            TokenKind::Exclamation => write!(f, "!"),
            TokenKind::Dot => write!(f, "."),
            TokenKind::Colon => write!(f, ":"),
            TokenKind::Semi => write!(f, ";"),
            TokenKind::Hash => write!(f, "#"),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Quote => write!(f, "\""),
            TokenKind::Delimiter(delim, left) => {
                if *left {
                    write!(f, "{}", delim.left())
                } else {
                    write!(f, "{}", delim.right())
                }
            }
            TokenKind::Unexpected(ch) => write!(f, "{}", ch),
            TokenKind::SingleQuote => write!(f, "'"),
            TokenKind::IntLiteral(num) => write!(f, "{}", num),
            TokenKind::FloatLiteral(num) => write!(f, "{}", num),
            TokenKind::CharLiteral(ch) => write!(f, "'{}'", ch),
            TokenKind::StrLiteral(str) => {
                write!(f, "\"{}\"", STRING_LITERAL_MAP.lookup(*str))
            }
            TokenKind::Keyword(kwd) => kwd.fmt(f),
            TokenKind::Ident(ident) => {
                write!(f, "{}", IDENTIFIER_MAP.ident_name(*ident))
            }
            TokenKind::Tree(delim, _) => {
                write!(f, "{}", delim.left())
            }
        }
    }
}

pub struct TokenKindVector(Vec<TokenKind>);

impl TokenKindVector {
    pub fn from_slice(items: &[TokenKind]) -> Self {
        Self(items.to_vec())
    }

    // @@Naming
    pub fn expression_glue() -> Self {
        Self(vec![
            TokenKind::Dot,
            TokenKind::Colon,
            TokenKind::Lt,
            TokenKind::Delimiter(Delimiter::Paren, true),
            TokenKind::Delimiter(Delimiter::Brace, true),
            TokenKind::Delimiter(Delimiter::Bracket, true),
        ])
    }
}

/// This is used within error messages, so it is formatted in a pretty way to display the expected token kinds
/// after a particular token. This is useful for constructing re-usable error messages that might appear in multiple
/// places when parsing. We use conjunctives to display multiple variants together, so they are readable. If the
/// length of the vector kind is one, we don't use conjunctives to glue kinds together.
/// @@Improvement: Multiple language support ???
impl fmt::Display for TokenKindVector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // This is where Haskell would really shine...
        match self.0.len() {
            0 => write!(f, ""),
            1 => write!(f, "{}", self.0.get(0).unwrap()),
            _ => {
                let mut items = self.0.iter().peekable();

                while let Some(item) = items.next() {
                    if items.peek().is_some() {
                        write!(f, "'{}', ", item)?;
                    } else {
                        write!(f, "'{}'", item)?;
                    };
                }

                write!(f, ".")
            }
        }
    }
}

/// A [TokenError] represents a encountered error during tokenisation, which includes an optional message
/// with the error, the [TokenErrorKind] which classifies the error, and a [ast::Location] that represents
/// where the tokenisation error occurred.
#[derive(Debug)]
pub struct TokenError {
    pub(crate) message: Option<String>,
    kind: TokenErrorKind,
    location: Location,
}

/// A [TokenErrorKind] represents the kind of [TokenError] which gives additional context to the error
/// with the provided message in [TokenError]
#[derive(Debug)]
pub enum TokenErrorKind {
    /// Occurs when a escape sequence (within a character or a string) is malformed.
    BadEscapeSequence,
    /// Occurs when a numerical literal doesn't follow the language specification, or is too large.
    MalformedNumericalLiteral,
    /// Occurs when a char is unexpected in the current context
    Unexpected(char),
    /// Occurs when the tokeniser expects a particular token next, but could not derive one.
    Expected(TokenKind),
    /// Unclosed tree block
    Unclosed(Delimiter),
}

impl TokenError {
    pub fn new(message: Option<String>, kind: TokenErrorKind, location: Location) -> Self {
        TokenError {
            message,
            kind,
            location,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        println!("{:?}", std::mem::size_of::<Delimiter>());
        println!("{:?}", std::mem::size_of::<Token>());
        println!("{:?}", std::mem::size_of::<TokenKind>());
    }
}
