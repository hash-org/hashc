//! File describing all the variants of Tokens that can be present within a
//! Hash source file.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::fmt;

use hash_alloc::collections::row::Row;
use hash_alloc::row;
use hash_alloc::Wall;
use hash_ast::ident::Identifier;
use hash_ast::ident::IDENTIFIER_MAP;
use hash_ast::keyword::Keyword;
use hash_ast::literal::{StringLiteral, STRING_LITERAL_MAP};
use hash_ast::location::Location;

pub type TokenResult<T> = Result<T, TokenError>;

/// A Lexeme token that represents the smallest code unit of a hash source file. The
/// token contains a kind which is elaborated by [TokenKind] and a [Location] in the
/// source that is represented as a span. The span is the beginning byte offset, and the
/// number of bytes for the said token.
#[derive(Debug, PartialEq)]
pub struct Token<'c> {
    pub kind: TokenKind<'c>,
    pub span: Location,
}

impl<'c> Token<'c> {
    pub fn new(kind: TokenKind<'c>, span: Location) -> Self {
        Token { kind, span }
    }

    pub fn has_kind(&self, right: TokenKind<'c>) -> bool {
        self.kind == right
    }

    pub fn has_atom(&self, right: TokenAtom) -> bool {
        match self.kind {
            TokenKind::Atom(left) => left == right,
            _ => false,
        }
    }

    pub fn is_brace_tree(&self) -> bool {
        matches!(self.kind, TokenKind::Tree(Delimiter::Brace, _))
    }

    pub fn clone_in(&self, wall: &Wall<'c>) -> Self {
        Token {
            kind: self.kind.clone_in(wall),
            span: self.span,
        }
    }
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TokenKind::Atom(TokenAtom::Ident(ident)) => {
                write!(f, "Ident ({})", IDENTIFIER_MAP.ident_name(*ident))
            }
            TokenKind::Tree(delim, tree) => {
                writeln!(f, "Delimiter({})", delim.left())?;

                for token in tree.iter() {
                    writeln!(f, "{}", token)?;
                }

                write!(f, "Delimiter({})", delim.right())
            }
            TokenKind::Atom(TokenAtom::StrLiteral(literal)) => {
                write!(
                    f,
                    "StringLiteral (\"{}\")",
                    STRING_LITERAL_MAP.lookup(*literal)
                )
            }
            // We want to print the actual character, instead of a potential escape code
            TokenKind::Atom(TokenAtom::CharLiteral(ch)) => {
                write!(f, "CharLiteral ('{}')", ch)
            }
            kind => write!(f, "{:?}", kind),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq)]
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

/// An Atom represents all variants of a token that can be present in a source file. Must of the
/// kinds only represen a single character, but some tokens account for an entire literal or an identifier.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum TokenAtom {
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
    StrLiteral(StringLiteral),
    /// Identifier
    Ident(Identifier),

    Keyword(Keyword),

    /// Delimiter: '(' '{', '[' and right hand-side variants, useful for error reporting and messages
    Delimiter(Delimiter, bool),

    /// @@Redundant: we should report an error on this?
    /// A token that was unexpected by the lexer, e.g. a unicode symbol not within
    /// string literal.
    Unexpected(char),
}

impl fmt::Display for TokenAtom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenAtom::Eq => write!(f, "="),
            TokenAtom::Lt => write!(f, ">"),
            TokenAtom::Gt => write!(f, ">"),
            TokenAtom::Plus => write!(f, "+"),
            TokenAtom::Minus => write!(f, "-"),
            TokenAtom::Star => write!(f, "*"),
            TokenAtom::Slash => write!(f, "/"),
            TokenAtom::Percent => write!(f, "%"),
            TokenAtom::Caret => write!(f, "^"),
            TokenAtom::Amp => write!(f, "&"),
            TokenAtom::Tilde => write!(f, "~"),
            TokenAtom::Pipe => write!(f, "|"),
            TokenAtom::Question => write!(f, "?"),
            TokenAtom::Exclamation => write!(f, "!"),
            TokenAtom::Dot => write!(f, "."),
            TokenAtom::Colon => write!(f, ":"),
            TokenAtom::Semi => write!(f, ";"),
            TokenAtom::Hash => write!(f, "#"),
            TokenAtom::Comma => write!(f, ","),
            TokenAtom::Quote => write!(f, "\""),
            TokenAtom::Delimiter(delim, left) => {
                if *left {
                    write!(f, "{}", delim.left())
                } else {
                    write!(f, "{}", delim.right())
                }
            }
            TokenAtom::Unexpected(ch) => write!(f, "{}", ch),
            TokenAtom::SingleQuote => write!(f, "'"),
            TokenAtom::IntLiteral(num) => write!(f, "{}", num),
            TokenAtom::FloatLiteral(num) => write!(f, "{}", num),
            TokenAtom::CharLiteral(ch) => write!(f, "'{}'", ch),
            TokenAtom::StrLiteral(str) => {
                write!(f, "\"{}\"", STRING_LITERAL_MAP.lookup(*str))
            }
            TokenAtom::Keyword(kwd) => kwd.fmt(f),
            TokenAtom::Ident(ident) => {
                write!(f, "{}", IDENTIFIER_MAP.ident_name(*ident))
            }
        }
    }
}

pub struct TokenKindVector<'c>(Row<'c, TokenKind<'c>>);

impl<'c> TokenKindVector<'c> {
    pub fn empty(wall: &Wall<'c>) -> Self {
        Self(row![wall])
    }

    pub fn from_row(items: Row<'c, TokenKind<'c>>) -> Self {
        Self(items)
    }

    // @@Naming
    pub fn expression_glue(wall: &Wall<'c>) -> Self {
        Self(row![wall;
            TokenKind::Atom(TokenAtom::Dot),
            TokenKind::Atom(TokenAtom::Colon),
            TokenKind::Atom(TokenAtom::Lt),
            TokenKind::Atom(TokenAtom::Delimiter(Delimiter::Paren, true)),
            TokenKind::Atom(TokenAtom::Delimiter(Delimiter::Brace, true)),
            TokenKind::Atom(TokenAtom::Delimiter(Delimiter::Bracket, true)),
        ])
    }
}

/// This is used within error messages, so it is formatted in a pretty way to display the expected token kinds
/// after a particular token. This is useful for constructing re-usable error messages that might appear in multiple
/// places when parsing. We use conjunctives to display multiple variants together, so they are readable. If the
/// length of the vector kind is one, we don't use conjunctives to glue kinds together.
/// @@Improvement: Multiple language support ???
impl fmt::Display for TokenKindVector<'_> {
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

#[derive(Debug, PartialEq)]
pub enum TokenKind<'c> {
    Atom(TokenAtom),

    /// A token tree is represnted by an arbitrary number of tokens that are surrounded by
    /// a given delimiter kind, the variants are specified in the [Delimiter] enum.
    Tree(Delimiter, Row<'c, Token<'c>>),
}

impl<'c> fmt::Display for TokenKind<'c> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Atom(atom) => atom.fmt(f),
            TokenKind::Tree(_, tokens) => write!(f, "{:?}", tokens),
        }
    }
}

impl<'c> TokenKind<'c> {
    pub(crate) fn clone_in(&self, wall: &Wall<'c>) -> Self {
        match self {
            TokenKind::Atom(atom) => TokenKind::Atom(*atom),
            TokenKind::Tree(delimeter, tokens) => TokenKind::Tree(
                *delimeter,
                Row::from_iter(tokens.iter().map(|t| t.clone_in(wall)), wall),
            ),
        }
    }

    /// Check if a [TokenKind] can be considered in a situation as a unary operator.
    pub(crate) fn is_unary_op(&self) -> bool {
        matches!(
            self,
            TokenKind::Atom(
                TokenAtom::Plus
                    | TokenAtom::Minus
                    | TokenAtom::Star
                    | TokenAtom::Slash
                    | TokenAtom::Amp
                    | TokenAtom::Tilde
                    | TokenAtom::Exclamation
            )
        )
    }

    /// Checks if the [TokenKind] must begin a statement, as in the specified keywords that
    /// follow a specific syntax, and must be statements.
    pub(crate) fn begins_statement(&self) -> bool {
        matches!(
            self,
            TokenKind::Atom(
                TokenAtom::Keyword(Keyword::Let)
                    | TokenAtom::Keyword(Keyword::For)
                    | TokenAtom::Keyword(Keyword::While)
                    | TokenAtom::Keyword(Keyword::Loop)
                    | TokenAtom::Keyword(Keyword::If)
                    | TokenAtom::Keyword(Keyword::Else)
                    | TokenAtom::Keyword(Keyword::Match)
                    | TokenAtom::Keyword(Keyword::Trait)
                    | TokenAtom::Keyword(Keyword::Enum)
                    | TokenAtom::Keyword(Keyword::Struct)
                    | TokenAtom::Keyword(Keyword::Continue)
                    | TokenAtom::Keyword(Keyword::Break)
                    | TokenAtom::Keyword(Keyword::Return)
            )
        )
    }

    /// Check if the [TokenKind] is a primitive literal; either a 'char', 'int', 'float' or a 'string'
    pub(crate) fn is_literal(&self) -> bool {
        matches!(
            self,
            TokenKind::Atom(
                TokenAtom::IntLiteral(_)
                    | TokenAtom::FloatLiteral(_)
                    | TokenAtom::CharLiteral(_)
                    | TokenAtom::StrLiteral(_)
            )
        )
    }
}

/// A [TokenError] represents a encountered error during tokenisation, which includes an optional message
/// with the error, the [TokenErrorKind] which classifies the error, and a [Location] that represents
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
    Expected(TokenAtom),
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
