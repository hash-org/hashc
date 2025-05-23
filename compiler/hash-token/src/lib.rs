//! Hash Compiler token definitions that are used by the lexer when lexing
//! the input sources.
pub mod cursor;
pub mod delimiter;
pub mod keyword;

use std::fmt;

use delimiter::Delimiter;
use hash_source::{
    constant::{AllocId, FloatTy, IntTy},
    identifier::Identifier,
    location::{ByteRange, SpannedSource},
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

    /// Pretty-print a token with reference to a [SpannedSource] in
    /// order to print literals.
    ///
    /// ##Note: this does not print trees.
    ///
    /// @@Todo: make this in a "TokenPrinter" context so that we don't
    /// need to explicitly make this a method on token.
    pub fn pretty_print(&self, source: SpannedSource<'_>) -> String {
        match self.kind {
            TokenKind::Int(_, _) | TokenKind::Float(_) | TokenKind::Char(_) | TokenKind::Str(_) => {
                source.hunk(self.span).to_string()
            }
            TokenKind::Tree(_, _) => {
                panic!("cannot pretty print token trees directly")
            }
            _ => format!("{}", self),
        }
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            TokenKind::Ident(ident) => {
                write!(f, "{}", String::from(*ident))
            }
            TokenKind::Str(_) | TokenKind::Char(_) | TokenKind::Int(_, _) | TokenKind::Float(_) => {
                panic!("cannot directly format literal token")
            }
            kind => write!(f, "{kind}"),
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
                    | TokenKind::At
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
                | TokenKind::Byte(_)
                | TokenKind::Float(_)
                | TokenKind::Char(_)
                | TokenKind::Str(_)
        )
    }

    /// Check if the [TokenKind] is a numeric literal
    #[inline]
    pub fn is_numeric(&self) -> bool {
        matches!(self, TokenKind::Int(_, _) | TokenKind::Byte(_) | TokenKind::Float(_))
    }

    /// Check if the [TokenKind] is a `range` like literal, i.e.
    /// it can feature within a range.
    #[inline]
    pub fn is_range_lit(&self) -> bool {
        matches!(
            self,
            TokenKind::Int(_, _) | TokenKind::Byte(_) | TokenKind::Float(_) | TokenKind::Char(_)
        )
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
    /// An access `::`
    Access,
    /// An ellipsis `...`
    Ellipsis,
    /// An inclusive range `..`
    Range,
    /// An exclusive range `..<`
    RangeExclusive,
    /// Integer Literal
    Int(Base, IntLitKind),
    /// Byte Literal
    Byte(u8),
    /// Float literal
    Float(FloatLitKind),
    /// Character literal.
    Char(char),
    /// String literal.
    Str(AllocId),
    /// Identifier.
    Ident(Identifier),

    /// Tree a token indicating the start of a token tree, i.e. some
    /// delimited block of tokens. The `u32` is the length of the tokens
    /// within the tree excluding the delimiters.
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
            TokenKind::Str(alloc) => format!("the string `{}`", alloc.to_str()),
            TokenKind::Keyword(kwd) => format!("the keyword `{kwd}`"),
            TokenKind::Ident(ident) => format!("the identifier `{}`", *ident),
            kind => format!("a `{kind}`"),
        }
    }

    /// Check if the [TokenKind] is a tree.
    pub fn is_tree(&self) -> bool {
        matches!(self, TokenKind::Tree(_, _))
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
            TokenKind::Ellipsis => write!(f, "..."),
            TokenKind::Range => write!(f, ".."),
            TokenKind::RangeExclusive => write!(f, "..<"),
            TokenKind::SingleQuote => write!(f, "'"),
            TokenKind::Unexpected(atom) => write!(f, "{atom}"),
            TokenKind::Int(_, _) => write!(f, "integer"),
            TokenKind::Byte(_) => write!(f, "byte"),
            TokenKind::Float(_) => write!(f, "float"),
            TokenKind::Char(ch) => write!(f, "'{ch}'"),
            TokenKind::LeftDelim(delim) => write!(f, "{}", delim.left()),
            TokenKind::RightDelim(delim) => write!(f, "{}", delim.right()),
            TokenKind::Tree(delim, _) => write!(f, "{}...{}", delim.left(), delim.right()),
            TokenKind::Str(str) => {
                let value = str.to_str();
                write!(f, "\"{}\"", value)
            }
            TokenKind::Keyword(kwd) => kwd.fmt(f),
            TokenKind::Ident(ident) => {
                write!(f, "{}", String::from(*ident))
            }
            TokenKind::Err => write!(f, "<error>"),
        }
    }
}
