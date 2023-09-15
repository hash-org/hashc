//! Hash Compiler token definitions that are used by the lexer when lexing
//! the input sources.
pub mod delimiter;
pub mod keyword;

use std::fmt;

use delimiter::Delimiter;
use hash_source::{
    constant::{FloatTy, IntTy, InternedStr},
    identifier::Identifier,
    location::ByteRange,
};
use keyword::Keyword;

/// A Lexeme token that represents the smallest code unit of a hash source file.
/// The token contains a kind which is elaborated by [TokenKind] and a
/// [ByteRange] in the source that is represented as a span. The span is the
/// beginning byte offset, and the number of bytes for the said token.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Token {
    /// The current token type.
    pub kind: TokenKind,
    /// The span of the current token.
    pub span: ByteRange,
}

impl Token {
    /// Create a new token from a kind and a provided [ByteRange].
    pub fn new(kind: TokenKind, span: ByteRange) -> Self {
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
            TokenKind::Str(lit) => {
                write!(f, "String (\"{}\")", String::from(*lit))
            }
            // We want to print the actual character, instead of a potential escape code
            TokenKind::Char(ch) => {
                write!(f, "Char ('{ch}')")
            }
            kind => write!(f, "{kind:?}"),
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
                    | TokenKind::Pound // directives
                    | TokenKind::Amp
                    | TokenKind::Tilde
                    | TokenKind::Exclamation
                    | TokenKind::Keyword(Keyword::Unsafe)
        )
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
                | TokenKind::Keyword(Keyword::If)
                | TokenKind::Keyword(Keyword::Match)
        )
    }

    /// Check if the [TokenKind] is a primitive literal, which is either: a
    /// 'char', 'int', 'float' or a 'string'
    pub fn is_lit(&self) -> bool {
        matches!(
            self,
            TokenKind::Keyword(Keyword::False)
                | TokenKind::Keyword(Keyword::True)
                | TokenKind::Int(_, _)
                | TokenKind::Float(_)
                | TokenKind::Char(_)
                | TokenKind::Str(_)
        )
    }

    /// Check if the [TokenKind] is a numeric literal
    #[inline]
    pub fn is_numeric(&self) -> bool {
        matches!(self, TokenKind::Int(_, _) | TokenKind::Float(_))
    }

    /// Check if the [TokenKind] is a `range` like literal, i.e.
    /// it can feature within a range.
    #[inline]
    pub fn is_range_lit(&self) -> bool {
        matches!(self, TokenKind::Int(_, _) | TokenKind::Float(_) | TokenKind::Char(_))
    }
}

/// The kind of ascription that is applied to the [FloatLit].
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FloatLitKind {
    /// Has a provided user suffix type
    Suffixed(FloatTy),
    /// No provided suffix type, so defaults to `f32`
    Unsuffixed,
}

impl fmt::Display for FloatLitKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FloatLitKind::Suffixed(ty) => write!(f, "{ty}"),
            FloatLitKind::Unsuffixed => write!(f, ""),
        }
    }
}

/// The type of the float the [IntLit] is storing.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum IntLitKind {
    /// integer kind `i128`, `u32` ,`i8`...
    Suffixed(IntTy),
    /// No provided suffix type, so defaults to `i32`
    Unsuffixed,
}

impl IntLitKind {
    /// Get the type of the integer literal
    pub fn ty(&self) -> IntTy {
        match self {
            IntLitKind::Suffixed(ty) => *ty,
            IntLitKind::Unsuffixed => IntTy::default(),
        }
    }
}

impl fmt::Display for IntLitKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntLitKind::Suffixed(ty) => write!(f, "{ty}"),
            IntLitKind::Unsuffixed => write!(f, ""),
        }
    }
}

/// Represents the featured base for numeric literals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Base {
    /// Binary base, denoted in literals as `0b101010`
    Binary,
    /// Octal base, denoted in literals as `0o26317261`
    Octal,
    /// Decimal base, written as `102391`
    Decimal,
    /// Hexadecimal base, written as `0xdeadbeef`
    Hex,
    /// Unsupported base, the language doesn't support the
    /// provided radix as a base.
    Unsupported,
}

impl fmt::Display for Base {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Base::Binary => write!(f, "binary"),
            Base::Octal => write!(f, "octal"),
            Base::Decimal => write!(f, "decimal"),
            Base::Hex => write!(f, "hexadecimal"),
            Base::Unsupported => write!(f, "unsupported base"),
        }
    }
}

impl From<Base> for u32 {
    fn from(base: Base) -> Self {
        match base {
            Base::Binary => 2,
            Base::Octal => 8,
            Base::Decimal => 10,
            Base::Hex => 16,
            Base::Unsupported => unreachable!("unsupported base"),
        }
    }
}

impl From<u32> for Base {
    fn from(radix: u32) -> Self {
        match radix {
            2 => Base::Binary,
            8 => Base::Octal,
            10 => Base::Decimal,
            16 => Base::Hex,
            _ => Base::Unsupported,
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
    Pound,
    /// `@`
    At,
    /// '$'
    Dollar,
    /// ','
    Comma,
    /// '"'
    Quote,
    /// "'"
    SingleQuote,
    /// A thin arrow `->`
    ThinArrow,
    /// A fat arrow `=>`
    FatArrow,
    /// A namespace access `::`
    Access,
    /// Integer Literal
    Int(Base, IntLitKind),
    /// Float literal
    Float(FloatLitKind),
    /// Character literal.
    Char(char),
    /// String literal.
    Str(InternedStr),
    /// Identifier.
    Ident(Identifier),

    /// Tree - The index is set as a `u32` since it isn't going
    /// to be the case that the index will or should ever really
    /// reach `2^32` since the index is per module and not per project.
    ///
    /// @@Todo: rather than using an index into the token trees, we should
    /// use it as a index into the token stream to denote where the
    /// token tree ends. This means that we can have a flat token
    /// stream which removes the need for storing token trees
    /// separately.
    Tree(Delimiter, u32),

    /// Keyword
    Keyword(Keyword),

    /// Delimiters `(`, `{`, `[`, doesn't include `<`.
    LeftDelim(Delimiter),

    /// Delimiters `)`, `}`, `]`, doesn't include `>`.
    RightDelim(Delimiter),

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
            TokenKind::Unexpected(atom) => format!("an unknown character `{atom}`"),
            TokenKind::Char(ch) => format!("`{ch}`"),
            TokenKind::Str(str) => format!("the string `{}`", *str),
            TokenKind::Keyword(kwd) => format!("the keyword `{kwd}`"),
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
            TokenKind::Pound => write!(f, "#"),
            TokenKind::At => write!(f, "@"),
            TokenKind::Dollar => write!(f, "$"),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Quote => write!(f, "\""),
            TokenKind::ThinArrow => write!(f, "->"),
            TokenKind::FatArrow => write!(f, "=>"),
            TokenKind::Access => write!(f, "::"),
            TokenKind::SingleQuote => write!(f, "'"),
            TokenKind::Unexpected(atom) => write!(f, "{atom}"),
            TokenKind::Int(_, _) => write!(f, "float"),
            TokenKind::Float(_) => write!(f, "integer"),
            TokenKind::Char(ch) => write!(f, "'{ch}'"),
            TokenKind::LeftDelim(delim) => write!(f, "{}", delim.left()),
            TokenKind::RightDelim(delim) => write!(f, "{}", delim.right()),
            TokenKind::Tree(delim, _) => write!(f, "{}...{}", delim.left(), delim.right()),
            TokenKind::Str(str) => {
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
