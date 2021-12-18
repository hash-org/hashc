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

use crate::error::TokenError;

pub type TokenResult<T> = Result<T, TokenError>;

/// A Lexeme token that represents the smallest code unit of a hash source file. The
/// token contains a kind which is elaborated by [TokenKind] and a [Location] in the
/// source that is represented as a span. The span is the beginning byte offset, and the
/// number of bytes for the said token.
#[derive(Debug, PartialEq)]
pub struct Token {
    /// The current token type.
    pub kind: TokenKind,
    /// The spanning location of the current token.
    pub span: Location,
}

impl Token {
    /// Create a new token from a kind and a provided location.
    pub fn new(kind: TokenKind, span: Location) -> Self {
        Token { kind, span }
    }

    /// Check if the token has the specified token kind.
    pub fn has_kind(&self, right: TokenKind) -> bool {
        self.kind == right
    }

    /// Function to convert a token into atom regardless whether the kind
    /// is a tree or an atom. If the token kind is a tree, the delimiter of the
    /// tree is used as the atom.
    // pub fn to_atom(&self) -> TokenKind {
    //     match self.kind {
    //         TokenKind::Tree(delim, _) => TokenKind::Delimiter(delim, true),
    //         TokenKind::Atom(atom) => atom,
    //     }
    // }

    /// Convert the current token into a tree provided that it is one. The
    /// function will panic if an attempt to convert a token atom into a
    /// tree.
    // pub fn into_tree(&self) -> (&Row<'c, Token<'c>>, Location) {
    //     let location = self.span;

    //     let tree = match &self.kind {
    //         TokenKind::Tree(_, tree) => tree,
    //         _ => unreachable!("Cannot convert token into tree"),
    //     };

    //     (tree, location)
    // }

    /// Check if the token is a tree and the tree beginning character
    /// is a brace.
    pub fn is_brace_tree(&self) -> bool {
        matches!(self.kind, TokenKind::Tree(Delimiter::Brace, _))
    }

    /// Check if the token is a tree and the tree beginning character
    /// is a parenthesis.
    pub fn is_paren_tree(&self) -> bool {
        matches!(self.kind, TokenKind::Tree(Delimiter::Paren, _))
    }

    // Copy the current token in the specified [Wall] allocator.
    // pub fn clone_in(&self, wall: &Wall<'c>) -> Self {
    //     Token {
    //         kind: self.kind.clone_in(wall),
    //         span: self.span,
    //     }
    // }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TokenKind::Ident(ident) => {
                write!(f, "Ident ({})", IDENTIFIER_MAP.ident_name(*ident))
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

// #[derive(Debug, PartialEq)]
// pub enum TokenKind<'c> {
//     /// A token atom is a singular token type.
//     Atom(TokenAtom),

//     /// A token tree is represented by an arbitrary number of token atoms that are surrounded by
//     /// a given delimiter kind, the variants are specified in the [Delimiter] enum.
//     Tree(Delimiter, Row<'c, Token<'c>>),
// }

// impl<'c> fmt::Display for TokenKind<'c> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         match self {
//             TokenKind::Atom(atom) => write!(f, "{}", atom),
//             TokenKind::Tree(_, tokens) => write!(f, "{:#?}", tokens),
//         }
//     }
// }

impl TokenKind {
    /// Clone the current kind in the specified [Wall] allocator.
    // pub(crate) fn clone_in(&self, wall: &Wall<'c>) -> Self {
    //     match self {
    //         TokenKind::Atom(atom) => TokenKind::Atom(*atom),
    //         TokenKind::Tree(delimiter, tokens) => TokenKind::Tree(
    //             *delimiter,
    //             Row::from_iter(tokens.iter().map(|t| t.clone_in(wall)), wall),
    //         ),
    //     }
    // }

    /// Convert the token kind into an atom. If the current token kind is a tree, the
    /// function will return the [Delimiter] of the token tree.
    // pub(crate) fn to_atom(&self) -> TokenKind {
    //     match self {
    //         TokenKind::Tree(delim, _) => TokenKind::Delimiter(*delim, true),
    //         TokenKind::Atom(atom) => *atom,
    //     }
    // }

    /// Check if a [TokenKind] can be considered in a situation as a unary operator.
    pub(crate) fn is_unary_op(&self) -> bool {
        matches!(
            self,
            TokenKind::Plus
                    | TokenKind::Minus
                    | TokenKind::Star
                    | TokenKind::Slash
                    | TokenKind::Hash // intrinsics
                    | TokenKind::Amp
                    | TokenKind::Tilde
                    | TokenKind::Exclamation
        )
    }

    /// Checks if the [TokenKind] must begin a block, as in the specified keywords that
    /// follow a specific syntax, and must be statements.
    pub(crate) fn begins_block(&self) -> bool {
        matches!(
            self,
            TokenKind::Keyword(Keyword::For)
                | TokenKind::Keyword(Keyword::While)
                | TokenKind::Keyword(Keyword::Loop)
                | TokenKind::Keyword(Keyword::If)
                | TokenKind::Keyword(Keyword::Match)
        )
    }

    /// Checks if the [TokenKind] must begin a statement, as in the specified keywords that
    /// follow a specific syntax, and must be statements.
    pub(crate) fn begins_statement(&self) -> bool {
        matches!(
            self,
            TokenKind::Keyword(Keyword::Let)
                | TokenKind::Keyword(Keyword::Trait)
                | TokenKind::Keyword(Keyword::Enum)
                | TokenKind::Keyword(Keyword::Struct)
                | TokenKind::Keyword(Keyword::Continue)
                | TokenKind::Keyword(Keyword::Break)
                | TokenKind::Keyword(Keyword::Return)
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

    pub fn from_right(ch: char) -> Option<Delimiter> {
        match ch {
            ')' => Some(Delimiter::Paren),
            ']' => Some(Delimiter::Bracket),
            '}' => Some(Delimiter::Brace),
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

/// Display implementation for [Delimiter], it's always assumed that it's asking for
/// the right hand-side variant of the delimiter.
impl fmt::Display for Delimiter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.right())
    }
}

/// An Atom represents all variants of a token that can be present in a source file. Atom token
/// kinds can represent a single character, literal or an identifier.
#[derive(Debug, PartialEq, Copy, Clone)]
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
    StrLiteral(StringLiteral),
    /// Identifier
    Ident(Identifier),

    /// Tree
    Tree(Delimiter, usize),

    /// Keyword
    Keyword(Keyword),

    /// General classification of an identifier
    // @@Cleanup: find a better way to describe when we expect an identifier
    GenericIdent,

    /// Delimiter: '(' '{', '[' and right hand-side variants, useful for error reporting and messages.
    /// The boolean flag represents if the delimiter is left or right, If it's true, then it is the left
    /// variant.
    Delimiter(Delimiter, bool),

    /// A token that was unexpected by the lexer, e.g. a unicode symbol not within
    /// string literal.
    Unexpected(char),
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Eq => write!(f, "="),
            TokenKind::Lt => write!(f, "<"),
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
            TokenKind::Tree(delim, _) => write!(f, "{} tree {}", delim.left(), delim.right()),
            TokenKind::Unexpected(ch) => write!(f, "{}", ch),
            TokenKind::SingleQuote => write!(f, "'"),
            TokenKind::IntLiteral(num) => write!(f, "{}", num),
            TokenKind::FloatLiteral(num) => write!(f, "{}", num),
            TokenKind::CharLiteral(ch) => write!(f, "'{}'", ch),
            TokenKind::StrLiteral(str) => {
                write!(f, "\"{}\"", STRING_LITERAL_MAP.lookup(*str))
            }
            TokenKind::Keyword(kwd) => kwd.fmt(f),
            TokenKind::GenericIdent => write!(f, "identifier"),
            TokenKind::Ident(ident) => {
                write!(f, "{}", IDENTIFIER_MAP.ident_name(*ident))
            }
        }
    }
}

/// This is a wrapper around a vector of token atoms that can represent the expected
/// tokens in a given context when transforming the token tree into and an AST.
/// The wrapper exists because once again you cannot specify implementations for types
/// that don't originate from the current crate.
///
/// TODO(alex): Instead of using a [TokenAtom], we should use an enum to custom
/// variants or descriptors such as 'operator'. Instead of token atoms we can just
/// the display representations of the token atoms. Or even better, we can use the
/// [`ToString`] trait and just auto cast into a string, whilst holding a vector of
/// strings.
#[derive(Debug)]
pub struct TokenKindVector<'c>(Row<'c, TokenKind>);

impl<'c> TokenKindVector<'c> {
    /// Create a new empty [TokenAtomVector].
    pub fn empty(wall: &Wall<'c>) -> Self {
        Self(row![wall;])
    }

    pub fn inner(&self) -> &Row<'c, TokenKind> {
        &self.0
    }

    /// Create a [TokenAtomVector] from a provided row of expected atoms.
    pub fn from_row(items: Row<'c, TokenKind>) -> Self {
        Self(items)
    }

    /// Check if the current [TokenAtomVector] is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Create a [TokenAtomVector] with a single atom.
    pub fn singleton(wall: &Wall<'c>, atom: TokenKind) -> Self {
        Self(row![wall; atom])
    }

    /// Tokens that can act as a expression connective
    pub fn begin_expression(wall: &Wall<'c>) -> Self {
        Self(row![wall;
            TokenKind::Delimiter(Delimiter::Paren, true),
            TokenKind::Dot, // OR an operator, OR '::'
            TokenKind::Semi,
        ])
    }

    /// Tokens expected when the parser expects a collection of patterns to be present.
    pub fn begin_pattern_collection(wall: &Wall<'c>) -> Self {
        Self(row![wall;
            TokenKind::Delimiter(Delimiter::Paren, true),
            TokenKind::Delimiter(Delimiter::Brace, true),
        ])
    }

    /// Tokens expected when a pattern begins in a match statement.
    pub fn begin_pattern(wall: &Wall<'c>) -> Self {
        Self(row![wall;
            TokenKind::GenericIdent,
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
impl fmt::Display for TokenKindVector<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // This is where Haskell would really shine...
        match self.0.len() {
            0 => write!(f, ""),
            1 => write!(f, "a '{}'", self.0.get(0).unwrap()),
            _ => {
                let len = self.0.len();
                let mut items = self.0.iter().peekable();

                write!(f, "either a ")?;
                let mut count = 0;

                while let Some(item) = items.next() {
                    if items.peek().is_some() {
                        if count == len - 2 {
                            write!(f, "'{}', or ", item)?;
                        } else {
                            write!(f, "'{}', ", item)?;
                        }
                    } else {
                        write!(f, "'{}'", item)?;
                    };
                    count += 1;
                }

                write!(f, ".")
            }
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
