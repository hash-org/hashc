//! Hash Compiler token definitions that are used by the lexer when lexing
//! the input sources.
pub mod delimiter;
pub mod keyword;

use std::fmt::Display;

use delimiter::{Delimiter, DelimiterVariant};
use hash_source::{
    constant::{InternedFloat, InternedInt, InternedStr},
    identifier::Identifier,
    location::Span,
};
use keyword::Keyword;
use smallvec::{smallvec, SmallVec};

/// A Lexeme token that represents the smallest code unit of a hash source file.
/// The token contains a kind which is elaborated by [TokenKind] and a [Span] in
/// the source that is represented as a span. The span is the beginning byte
/// offset, and the number of bytes for the said token.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Token {
    /// The current token type.
    pub kind: TokenKind,
    /// The span of the current token.
    pub span: Span,
}

impl Token {
    /// Create a new token from a kind and a provided [Span].
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Token { kind, span }
    }

    /// Check if the token has the specified token kind.
    pub fn has_kind(&self, right: TokenKind) -> bool {
        self.kind == right
    }

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
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            TokenKind::Ident(ident) => {
                write!(f, "Ident ({})", String::from(*ident))
            }
            TokenKind::StrLit(lit) => {
                write!(f, "String (\"{}\")", String::from(*lit))
            }
            // We want to print the actual character, instead of a potential escape code
            TokenKind::CharLit(ch) => {
                write!(f, "Char ('{}')", ch)
            }
            kind => write!(f, "{:?}", kind),
        }
    }
}

impl TokenKind {
    /// Check if a [TokenKind] can be considered in a situation as a unary
    /// operator.
    pub fn is_unary_op(&self) -> bool {
        matches!(
            self,
            TokenKind::Plus
                    | TokenKind::Minus
                    | TokenKind::Star
                    | TokenKind::Slash
                    | TokenKind::Hash // directives
                    | TokenKind::Amp
                    | TokenKind::Tilde
                    | TokenKind::Exclamation
                    | TokenKind::Keyword(Keyword::Unsafe)
        )
    }

    /// Check whether a token is a numeric prefix, either being `+` or `-`
    pub fn is_numeric_prefix(&self) -> bool {
        matches!(self, TokenKind::Plus | TokenKind::Minus)
    }

    /// Check if the current token can begin a pattern
    /// Checks if the [TokenKind] must begin a block, as in the specified
    /// keywords that follow a specific syntax, and must be statements.
    pub fn begins_block(&self) -> bool {
        matches!(
            self,
            TokenKind::Keyword(Keyword::For)
                | TokenKind::Keyword(Keyword::While)
                | TokenKind::Keyword(Keyword::Loop)
                | TokenKind::Keyword(Keyword::Mod)
                | TokenKind::Keyword(Keyword::If)
                | TokenKind::Keyword(Keyword::Match)
                | TokenKind::Keyword(Keyword::Impl)
        )
    }

    /// Check if the [TokenKind] is a primitive literal; either a 'char', 'int',
    /// 'float' or a 'string'
    pub fn is_lit(&self) -> bool {
        matches!(
            self,
            TokenKind::Keyword(Keyword::False)
                | TokenKind::Keyword(Keyword::True)
                | TokenKind::IntLit(_, _)
                | TokenKind::FloatLit(_, _)
                | TokenKind::CharLit(_)
                | TokenKind::StrLit(_)
        )
    }

    /// Check if the [TokenKind] is a numeric literal
    pub fn is_numeric(&self) -> bool {
        matches!(self, TokenKind::IntLit(_, _) | TokenKind::FloatLit(_, _))
    }
}

/// Whether or not a numeric [TokenKind] has a interpolated sign with
/// it.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum Sign {
    Minus,
    None,
}

impl Display for Sign {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sign::Minus => write!(f, "-"),
            Sign::None => Ok(()),
        }
    }
}

/// An [TokenKind] represents all variants of a token that can be present in a
/// source file. [TokenKind]s can represent a single character, literal or an
/// identifier.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
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
    /// '$'
    Dollar,
    /// ','
    Comma,
    /// '"'
    Quote,
    /// "'"
    SingleQuote,
    /// Integer Literal
    IntLit(Sign, InternedInt),
    /// Float literal
    FloatLit(Sign, InternedFloat),
    /// Character literal
    CharLit(char),
    /// StrLiteral,
    StrLit(InternedStr),
    /// Identifier
    Ident(Identifier),

    /// Tree - The index is set as a `u32` since it isn't going
    /// to be the case that the index will or should ever really
    /// reach `2^32` since the index is per module and not per project.
    Tree(Delimiter, u32),

    /// Keyword
    Keyword(Keyword),

    /// Delimiters `(`, `{`, `[` and right hand-side variants
    Delimiter(Delimiter, DelimiterVariant),

    /// A token that was unexpected by the lexer, e.g. a unicode symbol not
    /// within string literal.
    Unexpected(char),

    /// Error token within the tokenisation process, essentially aiding deferred
    /// error reporting
    Err,
}

impl TokenKind {
    /// This function is used to create an error message representing when a
    /// token was unexpectedly encountered or was expected in a particular
    /// context.
    pub fn as_error_string(&self) -> String {
        match self {
            TokenKind::Unexpected(atom) => format!("an unknown character `{}`", atom),
            TokenKind::IntLit(_, lit) => format!("`{lit}`"),
            TokenKind::FloatLit(_, lit) => format!("`{lit}`"),
            TokenKind::CharLit(ch) => format!("`{ch}`"),
            TokenKind::StrLit(str) => format!("the string `{}`", *str),
            TokenKind::Keyword(kwd) => format!("`{kwd}`"),
            TokenKind::Ident(ident) => format!("the identifier `{}`", *ident),
            kind => format!("a `{kind}`"),
        }
    }
}

impl std::fmt::Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
            TokenKind::Dollar => write!(f, "$"),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Quote => write!(f, "\""),
            TokenKind::SingleQuote => write!(f, "'"),
            TokenKind::Unexpected(atom) => write!(f, "{atom}"),
            TokenKind::IntLit(_, lit) => write!(f, "{lit}"),
            TokenKind::FloatLit(_, lit) => write!(f, "{lit}"),
            TokenKind::CharLit(ch) => write!(f, "'{ch}'"),
            TokenKind::Delimiter(delim, variant) => {
                if *variant == DelimiterVariant::Left {
                    write!(f, "{}", delim.left())
                } else {
                    write!(f, "{}", delim.right())
                }
            }
            TokenKind::Tree(delim, _) => write!(f, "{}...{}", delim.left(), delim.right()),
            TokenKind::StrLit(str) => {
                write!(f, "\"{}\"", *str)
            }
            TokenKind::Keyword(kwd) => kwd.fmt(f),
            TokenKind::Ident(ident) => {
                write!(f, "{}", String::from(*ident))
            }
            TokenKind::Err => write!(f, "<error>"),
        }
    }
}

/// This is a wrapper around a vector of token atoms that can represent the
/// expected tokens in a given context when transforming the token tree into and
/// an AST. The wrapper exists because once again you cannot specify
/// implementations for types that don't originate from the current crate.
///
/// @@TODO(alex): Instead of using a [TokenKind], we should use an enum to
/// custom variants or descriptors such as 'operator'. Instead of token atoms we
/// can just the display representations of the token atoms. Or even better, we
/// can use the [`ToString`] trait and just auto cast into a string, whilst
/// holding a vector of strings.
#[derive(Debug, Clone)]
pub struct TokenKindVector(SmallVec<[TokenKind; 2]>);

impl TokenKindVector {
    /// Create a new empty [TokenKindVector].
    pub fn empty() -> Self {
        Self(smallvec![])
    }

    pub fn inner(&self) -> &SmallVec<[TokenKind; 2]> {
        &self.0
    }

    pub fn into_inner(self) -> SmallVec<[TokenKind; 2]> {
        self.0
    }

    /// Create a [TokenKindVector] from a provided row of expected atoms.
    pub fn from_vec(items: SmallVec<[TokenKind; 2]>) -> Self {
        Self(items)
    }

    /// Check if the current [TokenKindVector] is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Create a [TokenKindVector] with a single atom.
    pub fn singleton(kind: TokenKind) -> Self {
        Self(smallvec![kind])
    }

    /// Create a [TokenKindVector] that provides tokens that can modify the
    /// visibility of a variable.
    pub fn begin_visibility() -> Self {
        Self(smallvec![TokenKind::Keyword(Keyword::Pub), TokenKind::Keyword(Keyword::Priv)])
    }
}
