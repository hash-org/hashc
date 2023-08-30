//! Hash Compiler Lexer crate.
#![feature(cell_update, let_chains)]

use std::{cell::Cell, iter, num::ParseIntError};

use error::{LexerDiagnostics, LexerError, LexerErrorKind, LexerResult, NumericLitKind};
use hash_reporting::diagnostic::AccessToDiagnosticsMut;
use hash_source::{
    constant::{
        FloatConstant, FloatConstantValue, IntConstant, IntConstantValue, IntTy, InternedFloat,
        SIntTy, UIntTy,
    },
    identifier::{Identifier, IDENTS},
    location::{ByteRange, Span},
    SourceId,
};
use hash_target::size::Size;
use hash_token::{
    delimiter::{Delimiter, DelimiterVariant},
    keyword::ident_is_keyword,
    Token, TokenKind,
};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use utils::is_id_start;

use crate::utils::is_id_continue;

pub mod error;
mod utils;

/// Representing the end of stream, or the initial character that is set as
/// 'prev' in a [Lexer] since there is no character before the start.
const EOF_CHAR: char = '\0';

/// The [Lexer] is a representation of the source in tokens that can be turned
/// into the AST. The [Lexer] has methods that can parse various token types
/// from the source, transform the entire contents into a vector of tokens and
/// some useful lexing utilities.
pub struct Lexer<'a> {
    /// Location of the lexer in the current stream.
    offset: Cell<usize>,

    /// The contents that are to be lexed.
    contents: &'a str,

    /// Representative module index of the current source.
    source_id: SourceId,

    // We store the size of the machine word in order to determine
    // how to tokenise `usize` and `isize` literals.
    ///
    /// The size of the machine word in bytes.
    ///
    /// @@Future: remove literal parsing until later when we can properly
    /// normalise everything, the lexer should just normalise this value.
    word_size: Size,

    /// Representing the last character the lexer encountered. This is only set
    /// by [Lexer::advance_token] so that [Lexer::eat_token_tree] can perform a
    /// check on if the token tree was closed up.
    previous_delimiter: Cell<Option<char>>,

    /// If the current token position is within a token tree
    within_token_tree: Cell<bool>,

    /// Token tree store, essentially a collection of token trees that are
    /// produced when the lexer encounters bracketed token streams.
    token_trees: Vec<Vec<Token>>,

    /// The lexer diagnostics store
    diagnostics: LexerDiagnostics,
}

impl<'a> Lexer<'a> {
    /// Create a new [Lexer] from the given string input.
    pub fn new(contents: &'a str, source_id: SourceId, word_size: Size) -> Self {
        Lexer {
            offset: Cell::new(0),
            source_id,
            within_token_tree: Cell::new(false),
            previous_delimiter: Cell::new(None),
            word_size,
            contents,
            token_trees: vec![],
            diagnostics: LexerDiagnostics::default(),
        }
    }

    /// Emit an error into [LexerDiagnostics] and also
    /// set `has_fatal_error` flag to true so that the
    /// lexer terminates on the next advancement.
    #[inline]
    fn emit_fatal_error(
        &mut self,
        message: Option<String>,
        kind: LexerErrorKind,
        span: ByteRange,
    ) -> TokenKind {
        self.diagnostics.has_fatal_error.set(true);
        self.emit_error(message, kind, span)
    }

    /// Put an error into the [LexerDiagnostics], whilst returning a
    /// [TokenKind::Err] in place of a lexed token.
    #[inline]
    fn emit_error(
        &mut self,
        message: Option<String>,
        kind: LexerErrorKind,
        span: ByteRange,
    ) -> TokenKind {
        self.add_error(LexerError { message, kind, location: Span { span, id: self.source_id } });

        TokenKind::Err
    }

    /// Create a Lexer error and return a [Result], but internally
    /// it is always the [Err] variant.
    #[inline]
    fn error<T>(
        &self,
        message: Option<String>,
        kind: LexerErrorKind,
        span: ByteRange,
    ) -> Result<T, LexerError> {
        Err(LexerError { message, kind, location: Span { span, id: self.source_id } })
    }

    /// Returns a reference to the stored token trees for the current job
    pub fn into_token_trees(self) -> Vec<Vec<Token>> {
        self.token_trees
    }

    /// Tokenise the given input stream
    pub fn tokenise(&mut self) -> Vec<Token> {
        // Avoid shebang at the start of the source...
        self.strip_shebang();

        std::iter::from_fn(|| self.advance_token()).collect::<Vec<_>>()
    }

    /// Returns amount of already consumed symbols.
    #[inline(always)]
    fn len_consumed(&self) -> usize {
        self.offset.get()
    }

    /// Peeks the next symbol from the input stream without consuming it.
    fn peek(&self) -> char {
        self.nth_char(0)
    }

    /// Peeks the second symbol from the input stream without consuming it.
    fn peek_second(&self) -> char {
        self.nth_char(1)
    }

    /// Get the remaining un-lexed contents as a raw string.
    unsafe fn as_slice(&self) -> &str {
        let offset = self.offset.get();

        // ##Safety: We rely that the byte offset is correctly computed when stepping
        // over the characters in the iterator.
        std::str::from_utf8_unchecked(self.contents.as_bytes().get_unchecked(offset..))
    }

    /// Returns nth character relative to the current position.
    /// If requested position doesn't exist, `EOF_CHAR` is returned.
    /// However, getting `EOF_CHAR` doesn't always mean actual end of file,
    /// it should be checked with `is_eof` method.
    fn nth_char(&self, n: usize) -> char {
        let slice = unsafe { self.as_slice() };

        slice.chars().nth(n).unwrap_or(EOF_CHAR)
    }

    /// Moves to the next character.
    fn next(&mut self) -> Option<char> {
        let slice = unsafe { self.as_slice() };
        let ch = slice.chars().next()?;

        self.offset.update(|x| x + ch.len_utf8());
        Some(ch)
    }

    /// Move to the next character and skip it essentially.
    fn skip(&self) {
        let slice = unsafe { self.as_slice() };
        let ch = slice.chars().next().unwrap();

        // only increment the offset by one if there is a next character
        self.offset.update(|x| x + ch.len_utf8());
    }

    /// Checks if there is nothing more to consume.
    fn is_eof(&self) -> bool {
        self.contents.len() == self.len_consumed()
    }

    /// Strip the shebang, e.g. "#!/usr/bin/hashc", from a source assuming that
    /// this is the start of the file.
    fn strip_shebang(&mut self) {
        if self.peek() == '#' && self.peek_second() == '!' {
            self.eat_while_and_discard(|c| c != '\n');
        }
    }

    /// Parses a token from the input string.
    pub fn advance_token(&mut self) -> Option<Token> {
        // Eat any comments or whitespace before processing the token...
        loop {
            match self.peek() {
                c if c.is_whitespace() => self.eat_while_and_discard(char::is_whitespace),
                '/' => match self.peek_second() {
                    '*' => self.block_comment(),
                    '/' => self.line_comment(),
                    _ => {
                        self.skip();

                        let offset = self.offset.get();

                        // @@Hack: since we already compare if the first item is a slash, we'll just
                        // return here the slash and advance it by one.
                        return Some(Token::new(
                            TokenKind::Slash,
                            ByteRange::new(offset, offset + 1),
                        ));
                    }
                },
                _ => break,
            }
        }

        let offset = self.offset.get();
        let next_token = self.next();

        next_token?;

        // We avoid checking if the tokens are compound here because we don't really
        // want to deal with comments and spaces in an awkward way... Once the
        // whole stream is transformed into a bunch of tokens, we can then
        // combine these tokens into more complex variants that might span multiple
        // characters. For example, the code...
        // > ':' => match self.peek() {
        // >   ':' => {
        // > self.next();
        // > break TokenKind::NameAccess
        // > }
        // >   _ => break TokenKind::Colon
        // > },
        //
        // could work here, but however what about if there was a space or a comment
        // between the colons, this might be problematic. Essentially, we pass
        // the responsibility of forming more compound tokens to AST gen rather than
        // here.
        let token_kind = match next_token.unwrap() {
            // One-symbol tokens
            '~' => TokenKind::Tilde,
            '=' => TokenKind::Eq,
            '!' => TokenKind::Exclamation,
            '+' => TokenKind::Plus,
            '*' => TokenKind::Star,
            '%' => TokenKind::Percent,
            '>' => TokenKind::Gt,
            '<' => TokenKind::Lt,
            '|' => TokenKind::Pipe,
            '^' => TokenKind::Caret,
            '&' => TokenKind::Amp,
            ':' => TokenKind::Colon,
            ';' => TokenKind::Semi,
            ',' => TokenKind::Comma,
            '.' => TokenKind::Dot,
            '#' => TokenKind::Pound,
            '$' => TokenKind::Dollar,
            '?' => TokenKind::Question,

            // Consume a token tree, which is a starting delimiter, followed by a an arbitrary
            // number of tokens and closed by a following delimiter...
            ch @ ('(' | '{' | '[') => self.eat_token_tree(Delimiter::from_left(ch).unwrap()),

            // Identifier (this should be checked after other variant that can
            // start as identifier).
            ch if is_id_start(ch) => self.ident(ch),
            // If the next character is not a digit, then we just stop.
            '-' => TokenKind::Minus,
            // Numeric literal.
            ch @ '0'..='9' => self.number(ch),
            // character literal.
            '\'' => self.char(),
            // String literal.
            '"' => self.string(),

            // We have to exit the current tree if we encounter a closing delimiter...
            ch @ (')' | '}' | ']') if self.within_token_tree.get() => {
                self.previous_delimiter.set(Some(ch));
                return None;
            }
            ')' => TokenKind::Delimiter(Delimiter::Paren, DelimiterVariant::Right),
            '}' => TokenKind::Delimiter(Delimiter::Brace, DelimiterVariant::Right),
            ']' => TokenKind::Delimiter(Delimiter::Bracket, DelimiterVariant::Right),
            // We didn't get a hit on the right token...
            ch => TokenKind::Unexpected(ch),
        };

        // If we encountered a unrecoverable error, then terminate
        if self.diagnostics.has_fatal_error.get() {
            return None;
        }

        let location = ByteRange::new(offset, self.len_consumed());
        Some(Token::new(token_kind, location))
    }

    /// This will essentially recursively consume tokens until it reaches the
    /// right hand-side variant of the provided delimiter. If no delimiter
    /// is reached, but the stream has reached EOF, this is reported
    /// as an error because it is essentially an un-closed block. This kind of
    /// behaviour is desired and avoids performing complex delimiter depth
    /// analysis later on.
    fn eat_token_tree(&mut self, delimiter: Delimiter) -> TokenKind {
        let mut children_tokens = vec![];
        let start = self.offset.get() - 1; // we need to ge the previous location to accurately denote the error...

        // we need to reset self.prev here as it might be polluted with previous token
        // trees
        self.previous_delimiter.set(None);
        let prev_in_token_tree = self.within_token_tree.replace(true);

        while !self.is_eof() {
            // `None` here doesn't just mean EOF, it could also be that
            // the next token failed to be parsed.
            match self.advance_token() {
                Some(token) => children_tokens.push(token),
                None => break,
            };
        }

        self.within_token_tree.replace(prev_in_token_tree);

        // If there is a fatal error, then we need to abort
        if self.diagnostics.has_fatal_error.get() {
            return TokenKind::Err;
        }

        match self.previous_delimiter.get() {
            Some(delim) if delim == delimiter.right() => {
                // push this to the token_trees and get the current index to use instead...
                self.token_trees.push(children_tokens);
                self.previous_delimiter.set(None);

                TokenKind::Tree(delimiter, (self.token_trees.len() - 1) as u32)
            }
            _ => self.emit_error(
                None,
                LexerErrorKind::Unclosed(delimiter),
                ByteRange::new(start, start + 1),
            ),
        }
    }

    /// Consume an identifier, at this stage keywords are also considered to be
    /// identifiers. The function expects that the first character of the
    /// identifier is consumed when the function is called.
    fn ident(&mut self, first: char) -> TokenKind {
        debug_assert!(is_id_start(first));

        let start = self.offset.get() - first.len_utf8();
        // @@Hack: instead of using an iterator to collect, we want to eat the chars and
        // then take a slice at the end
        self.eat_while_and_discard(is_id_continue);

        let name = &self.contents[start..self.offset.get()];

        ident_is_keyword(name)
            .map_or_else(|| TokenKind::Ident(name.into()), |keyword| TokenKind::Keyword(keyword))
    }

    fn parse_int_value(
        &mut self,
        chars: &str,
        radix: u32,
        annotation_ty: Option<IntTy>,
    ) -> Result<IntConstantValue, ParseIntError> {
        // If the type is provided on the integer literal, then we
        // can directly just use the provided type as the parsing...
        if let Some(ty) = annotation_ty {
            match ty.normalise(self.word_size) {
                IntTy::Int(SIntTy::I8) => {
                    let value = i8::from_str_radix(chars, radix)?;
                    Ok(IntConstantValue::I8(value))
                }
                IntTy::Int(SIntTy::I16) => {
                    let value = i16::from_str_radix(chars, radix)?;
                    Ok(IntConstantValue::I16(value))
                }
                IntTy::Int(SIntTy::I32) => {
                    let value = i32::from_str_radix(chars, radix)?;
                    Ok(IntConstantValue::I32(value))
                }
                IntTy::Int(SIntTy::I64) => {
                    let value = i64::from_str_radix(chars, radix)?;
                    Ok(IntConstantValue::I64(value))
                }
                IntTy::Int(SIntTy::I128) => {
                    let value = i128::from_str_radix(chars, radix)?;
                    Ok(IntConstantValue::I128(value))
                }
                IntTy::UInt(UIntTy::U8) => {
                    let value = u8::from_str_radix(chars, radix)?;
                    Ok(IntConstantValue::U8(value))
                }
                IntTy::UInt(UIntTy::U16) => {
                    let value = u16::from_str_radix(chars, radix)?;
                    Ok(IntConstantValue::U16(value))
                }
                IntTy::UInt(UIntTy::U32) => {
                    let value = u32::from_str_radix(chars, radix)?;
                    Ok(IntConstantValue::U32(value))
                }
                IntTy::UInt(UIntTy::U64) => {
                    let value = u64::from_str_radix(chars, radix)?;
                    Ok(IntConstantValue::U64(value))
                }
                IntTy::UInt(UIntTy::U128) => {
                    let value = u128::from_str_radix(chars, radix)?;
                    Ok(IntConstantValue::U128(value))
                }

                IntTy::Int(SIntTy::IBig) | IntTy::UInt(UIntTy::UBig) => {
                    let value = BigInt::parse_bytes(chars.as_bytes(), radix).unwrap();
                    Ok(IntConstantValue::Big(Box::new(value)))
                }

                // We don't directly deal with usizes/isizes since we just normalised them.
                _ => unreachable!(),
            }
        } else {
            // If the type is not provided, then we try parse the type as a big-int and then
            // we try and shrink it into an `i32` since this is the default type. If this is
            // not successful, then the integer remains as a big-int which will likely be
            // converted to a `usize` or `isize` later on.
            let value = BigInt::parse_bytes(chars.as_bytes(), radix).unwrap();

            if let Some(value) = value.to_i32() {
                Ok(IntConstantValue::I32(value))
            } else {
                Ok(IntConstantValue::Big(Box::new(value)))
            }
        }
    }

    /// Function to create an integer constant from characters and
    /// a specific radix.
    fn create_int_const(
        &mut self,
        chars: &str,
        radix: u32,
        suffix: Option<Identifier>,
        start_pos: usize,
    ) -> TokenKind {
        // If we have a suffix, then we immediately try and parse it as a type.
        let ty = suffix.map(|suffix| match suffix.try_into() {
            Ok(ty) => ty,
            Err(_) => {
                self.emit_error(
                    None,
                    LexerErrorKind::InvalidLitSuffix(NumericLitKind::Integer, suffix),
                    ByteRange::new(self.offset.get(), self.offset.get()),
                );

                IntTy::Int(SIntTy::I32)
            }
        });

        // Based on the type, we then parse the contents as a specific type.
        let value = self.parse_int_value(chars, radix, ty).unwrap_or_else(|_| {
            self.emit_error(
                None,
                LexerErrorKind::MalformedNumericalLit,
                ByteRange::new(start_pos, self.offset.get()),
            );

            // It doesn't matter what we return here since we will terminate on the
            // next lex anyway.
            IntConstantValue::I32(0)
        });

        TokenKind::IntLit(IntConstant::new(value, suffix).into())
    }

    /// Attempt to eat an identifier if the next token is one, otherwise don't
    /// do anything
    fn maybe_eat_identifier(&self) -> Option<Identifier> {
        match self.peek() {
            ch if is_id_start(ch) => {
                self.skip();
                let start = self.offset.get() - ch.len_utf8();

                self.eat_while_and_discard(is_id_continue);
                let name = &self.contents[start..self.offset.get()];

                Some(name.into())
            }
            _ => None,
        }
    }

    /// Consume a number literal, either float or integer. The function expects
    /// that the first character of the numeric literal is consumed when the
    /// function is called.
    fn number(&mut self, prev: char) -> TokenKind {
        // record the start location of the literal
        let start = self.offset.get() - 1;

        // firstly, figure out if this literal has a base, if so then we need to perform
        // some magic at the end to cast it into the correct base...
        if prev == '0' {
            let maybe_radix = match self.peek() {
                'b' => Some(2),
                'o' => Some(8),
                'd' => Some(10),
                'x' => Some(16),
                _ => None,
            };

            // if this does have a radix then we need to handle the radix
            if let Some(radix) = maybe_radix {
                self.skip(); // accounting for the radix
                let chars = self.eat_decimal_digits(radix).to_string();

                // If we didn't get any characters, this means that
                if chars.is_empty() {
                    // @@Future: we want to return a `IntLit` token, and recover since this is not a
                    // fatal error...
                    return self.emit_error(
                        None,
                        LexerErrorKind::MissingDigits,
                        ByteRange::new(start, self.offset.get()),
                    );
                }

                let suffix = self.maybe_eat_identifier();

                // If this specifies a radix, and then also has a suffix which denotes
                // that this literal is a `float`, then we error since we don't support
                // non-decimal float literals.
                if matches!(suffix, Some(s) if s == IDENTS.f32 || s == IDENTS.f64) && radix != 10 {
                    // @@Future: we want to return a `IntLit` token, and recover since this is not a
                    // fatal error...
                    return self.emit_error(
                        None,
                        LexerErrorKind::UnsupportedFloatBaseLiteral(radix.into()),
                        ByteRange::new(start, self.offset.get()),
                    );
                } else {
                    return self.create_int_const(chars.as_str(), radix, suffix, start);
                }
            }
        }

        // @@Performance: could avoid allocating the string here?
        let pre_digits = iter::once(prev)
            .chain(self.eat_decimal_digits(10).chars())
            .filter(|c| *c != '_')
            .collect::<String>();

        // peek next to check if this is an actual float literal...
        match self.peek() {
            // here we have to check if the next char valid char is potentially a character that
            // begins an identifier. This enables for infix calls on integer literals in
            // the form of '2.pow(...)' If we don't check this here, it leads to the
            // tokeniser being too greedy and eating the 'dot' without reason.
            // Admittedly, this is a slight ambiguity in the language syntax, but
            // there isn't currently a clear way to resolve this ambiguity.
            '.' if !is_id_start(self.peek_second()) && self.peek_second() != '.' => {
                self.skip();

                let after_digits = self.eat_decimal_digits(10);

                let num = pre_digits
                    .chars()
                    .chain(std::iter::once('.'))
                    .chain(after_digits.chars().filter(|c| *c != '_'))
                    .collect::<String>();

                self.eat_float_lit(num.chars(), start)
            }
            // Immediate exponent
            'e' | 'E' => self.eat_float_lit(pre_digits.chars(), start),
            _ => {
                let suffix = self.maybe_eat_identifier();

                // If the suffix is equal to a float-like one, convert this token into
                // a `float`...
                if matches!(suffix, Some(s) if s == IDENTS.f32 || s == IDENTS.f64) {
                    match pre_digits.parse::<f64>() {
                        Err(err) => self.emit_error(
                            Some(format!("{err}.")),
                            LexerErrorKind::MalformedNumericalLit,
                            ByteRange::new(start, self.offset.get()),
                        ),
                        Ok(parsed) => {
                            // Create interned float constant
                            let float_const = if let Some(suffix_ident) = suffix && suffix_ident == IDENTS.f32 {
                                FloatConstantValue::F32(parsed as f32)
                            } else {
                                FloatConstantValue::F64(parsed)
                            };

                            TokenKind::FloatLit(InternedFloat::create(FloatConstant {
                                value: float_const,
                                suffix,
                            }))
                        }
                    }
                } else {
                    self.create_int_const(pre_digits.as_str(), 10, suffix, start)
                }
            }
        }
    }

    /// Function to apply an exponent to a floating point literal.
    fn eat_float_lit(&mut self, num: impl Iterator<Item = char>, start: usize) -> TokenKind {
        match num.collect::<String>().parse::<f64>() {
            Err(err) => self.emit_error(
                Some(format!("{err}.")),
                LexerErrorKind::MalformedNumericalLit,
                ByteRange::new(start, self.offset.get()),
            ),
            Ok(value) => {
                match self.eat_exponent(start) {
                    Ok(exp) => {
                        // if an exponent was specified, as in it is non-zero, we need to apply the
                        // exponent to the float literal.
                        let value = if exp != 0 { value * 10f64.powi(exp) } else { value };

                        // Get the type ascription if any...
                        let suffix = self.maybe_eat_identifier();

                        // Create interned float constant
                        let float_const = if let Some(suffix_ident) = suffix && suffix_ident == IDENTS.f32 {
                            FloatConstantValue::F32(value as f32)
                        } else {
                            // Check that the suffix is correct for the literal
                            if let Some(suffix_ident) = suffix && suffix_ident != IDENTS.f64 {
                                self.emit_error(
                                    None,
                                    LexerErrorKind::InvalidLitSuffix(NumericLitKind::Float, suffix_ident),
                                    ByteRange::new(start, self.offset.get()),
                                );
                            }

                            FloatConstantValue::F64(value)
                        };

                        TokenKind::FloatLit(InternedFloat::create(FloatConstant {
                            value: float_const,
                            suffix,
                        }))
                    }
                    Err(err) => {
                        self.add_error(err);
                        TokenKind::Err
                    }
                }
            }
        }
    }

    /// Consume an exponent for a float literal.
    fn eat_exponent(&mut self, start: usize) -> LexerResult<i32> {
        if !matches!(self.peek(), 'e' | 'E') {
            // @@Hack: we return a zero to signal that there was no exponent and therefore
            // avoid applying it later
            return Ok(0);
        }

        self.skip(); // consume the exponent

        // Check if there is a sign before the digits start in the exponent...
        let negated = if self.peek() == '-' {
            self.skip();
            true
        } else {
            false
        };

        // Check that there is at least on digit in the exponent
        if self.peek() == EOF_CHAR {
            return self.error(
                None,
                LexerErrorKind::MissingExponentDigits,
                ByteRange::new(start, self.offset.get()),
            );
        }

        match self.eat_decimal_digits(10).parse::<i32>() {
            Err(_) => self.error(
                Some("Invalid float exponent.".to_string()),
                LexerErrorKind::MalformedNumericalLit,
                ByteRange::new(start, self.offset.get() + 1),
            ),
            Ok(num) if negated => Ok(-num),
            Ok(num) => Ok(num),
        }
    }

    /// Consume only decimal digits up to encountering a non-decimal digit
    /// whilst taking into account that the language supports '_' as digit
    /// separators which should just be skipped over...
    fn eat_decimal_digits(&self, radix: u32) -> &str {
        self.eat_while_and_slice(move |c| c.is_digit(radix) || c == '_')
    }

    /// Transform an ordinary character into a well known escape sequence
    /// specified by the escape literal rules. More information about the
    /// escape sequences can be found at [escape sequences](https://hash-org.github.io/lang/basics/intro.html)
    fn char_from_escape_seq(&mut self) -> LexerResult<char> {
        let c = self.next().unwrap();

        // we need to compute the old byte offset by accounting for both the 'u'
        // character and the '\\' character, but since this is known to be 2
        // bytes, we can just subtract it from the current offset
        let start = self.offset.get() - 1;
        match c {
            '0' => Ok('\0'),
            'n' => Ok('\n'),
            't' => Ok('\t'),
            'u' => {
                // The next character should be a '{', otherwise this isn't a correct escaped
                // literal
                if self.peek() != '{' {
                    return self.error(
                        Some("Expected `{` after a `\\u` escape sequence".to_string()),
                        LexerErrorKind::BadEscapeSequence,
                        ByteRange::new(start, self.offset.get()),
                    );
                }

                self.skip(); // Eat the '{' beginning part of the scape sequence

                // here we expect up to 6 hex digits, which is finally closed by a '}'
                let chars = self.eat_while_and_slice(|c| c.is_ascii_hexdigit()).to_string();

                if self.peek() != '}' {
                    return self.error(
                        Some("expected `}` after a escape sequence".to_string()),
                        LexerErrorKind::BadEscapeSequence,
                        ByteRange::new(self.offset.get(), self.offset.get() + 1),
                    );
                }
                self.skip(); // Eat the '}' ending part of the scape sequence

                if chars.len() > 6 {
                    return self.error(
                        Some("Unicode escape literal must be at most 6 hex digits".to_string()),
                        LexerErrorKind::BadEscapeSequence,
                        ByteRange::new(start, self.offset.get()),
                    );
                }

                let value = u32::from_str_radix(chars.as_str(), 16);

                if value.is_err() {
                    return self.error(
                        Some(
                            "Unicode escape literal must only be comprised of hex digits"
                                .to_string(),
                        ),
                        LexerErrorKind::BadEscapeSequence,
                        ByteRange::new(start, self.offset.get()),
                    );
                }

                Ok(char::from_u32(value.unwrap()).unwrap())
            }
            'x' => {
                // Examples of the \x.. Escape sequence would be things like `\x07` or `\x0b`,
                // Essentially 2 hex_ascii_digits and the rest is not part of
                // the escape sequence and can be left alone.
                let chars: Result<String, LexerError> = (0..2)
                    .map(|_| match self.peek() {
                        c if c.is_ascii_hexdigit() => Ok(self.next().unwrap()),
                        EOF_CHAR => self.error(
                            Some("ASCII escape code too short".to_string()),
                            LexerErrorKind::BadEscapeSequence,
                            ByteRange::new(start, self.offset.get()),
                        ),
                        c => self.error(
                            Some("ASCII escape code must only contain hex digits".to_string()),
                            LexerErrorKind::Unexpected(c),
                            ByteRange::new(start, self.offset.get()),
                        ),
                    })
                    .collect();

                let chars = chars?;

                // ##Safety: Safe to unwrap since we check that both chars are hex valid and two
                // hex chars will always to fit into a u32
                let value = u32::from_str_radix(chars.as_str(), 16).unwrap();

                Ok(char::from_u32(value).unwrap())
            }
            'a' => Ok('\x07'),
            'b' => Ok('\x08'),
            'f' => Ok('\x1b'),
            'r' => Ok('\r'),
            'v' => Ok('\x0b'),
            '\\' => Ok('\\'),
            '"' => Ok('\"'),
            '\'' => Ok('\''),
            ch => self.error(
                Some(format!("unknown escape sequence `{ch}`")),
                LexerErrorKind::BadEscapeSequence,
                ByteRange::new(start, start + 1),
            ),
        }
    }

    /// Consume a char literal provided that the current previous token is a
    /// single quote, this will produce a [TokenKind::CharLit] provided
    /// that the literal is correctly formed and is ended before the end of
    /// file is reached. This function expects the the callee has previously
    /// eaten the starting single quote.
    fn char(&mut self) -> TokenKind {
        // Subtract one to capture the previous quote, since we know it's one byte in
        // size
        let start = self.offset.get() - 1;

        // check whether the next character is a backslash, as in escaping a char, if
        // not eat the next char and expect the second character to be a "\'"
        // char...
        if self.peek_second() == '\'' && self.peek() != '\\' {
            let ch = self.next().unwrap();
            self.skip();

            return TokenKind::CharLit(ch);
        } else if self.peek() == '\\' {
            // otherwise, this is an escaped char and hence we eat the '\' and use the next
            // char as the actual char by escaping it
            self.skip();

            match self.char_from_escape_seq() {
                Ok(ch) => {
                    let next = self.peek();

                    // eat the single quote after the character
                    if next != '\'' {
                        let offset = self.offset.get();

                        // @@Improvement: Maybe make this a function to check if we're about to hit
                        // the end...
                        if next == EOF_CHAR {
                            return self.emit_error(
                                Some("unclosed character literal".to_string()),
                                LexerErrorKind::Expected(TokenKind::SingleQuote),
                                ByteRange::new(offset, offset + 1),
                            );
                        }

                        return self.emit_error(
                            Some("character literal can only contain one codepoint".to_string()),
                            LexerErrorKind::BadEscapeSequence,
                            ByteRange::new(start, offset),
                        );
                    }

                    self.skip(); // eat the ending part of the character literal `'`

                    return TokenKind::CharLit(ch);
                }
                Err(err) => {
                    // Add the error to the diagnostics, and then try to recover by seeing if we can
                    // get the next token to be a `'`
                    self.add_error(err);

                    if self.peek() != '\'' {
                        self.diagnostics.has_fatal_error.set(true);
                    }
                    self.skip(); // Recover...

                    return TokenKind::Err;
                }
            };
        }

        // So here we know that this is an invalid character literal, to improve
        // the reporting aspect, we want to eat up until the next `'` in order
        // to highlight the entire literal
        let lit = self.eat_while_and_slice(move |c| c != '\'' && !c.is_whitespace()).to_string();

        // @@ErrorReporting: essentially we jump over the erroneous character literal
        // and continue lexing
        if !self.is_eof() {
            self.skip();
        }

        self.emit_error(
            None,
            LexerErrorKind::InvalidCharacterLit(lit),
            ByteRange::new(start, self.offset.get()),
        )
    }

    /// Consume a string literal provided that the current previous token is a
    /// double quote, this will produce a [TokenKind::StrLit] provided
    /// that the literal is correctly formed and is ended before the end of
    /// file is reached.
    fn string(&mut self) -> TokenKind {
        let mut value = String::from("");
        let mut closed = false;

        let start = self.offset.get();

        while let Some(c) = self.next() {
            match c {
                '"' => {
                    closed = true;
                    break;
                }
                '\\' => match self.char_from_escape_seq() {
                    Ok(ch) => value.push(ch),
                    Err(err) => {
                        self.add_error(err);
                        return TokenKind::Err;
                    }
                },
                ch => value.push(ch),
            }
        }

        // Report that the literal is unclosed and set the error as being fatal
        if !closed {
            // If we have a windows line ending, we want to use the offset before
            // the current so we're not highlighing the `\r` as well
            if value.len() >= 2 && &value[(value.len() - 2)..] == "\r\n" {
                self.offset.set(self.offset.get() - 1);
            }

            return self.emit_fatal_error(
                None,
                LexerErrorKind::UnclosedStringLit,
                ByteRange::new(start, self.offset.get()),
            );
        }

        // Essentially we put the string into the literal map and get an id out which we
        // use for the actual representation in the token
        TokenKind::StrLit(value.into())
    }

    /// Consume a line comment after the first following slash, essentially
    /// eating characters up to the next `\n` encountered. If we reach `EOF`
    /// before a newline, then we stop eating there.
    ///
    /// @@DocSupport: These could return a TokenKind so that we can feed it into
    /// some kind of documentation generator tool
    fn line_comment(&mut self) {
        debug_assert!(self.peek() == '/' && self.peek_second() == '/');
        self.skip();
        self.eat_while_and_discard(|c| c != '\n');
    }

    /// Consume a block comment after the first following `/*a` sequence of
    /// characters. If the iterator encounters the start of another block
    /// comment, we increment a nested comment counter to ensure that nested
    /// block comments are accounted for and handled gracefully.
    ///
    /// @@DocSupport: These could return a TokenKind so that we can feed it into
    /// some kind of documentation generator tool
    fn block_comment(&mut self) {
        debug_assert!(self.peek() == '/' && self.peek_second() == '*');
        self.skip();

        // since we aren't as dumb as C++, we want to count the depth of block comments
        // and account for nested ones, we keep track of it whilst consuming the
        // block...
        let mut depth: u32 = 1;

        while let Some(c) = self.next() {
            match c {
                '/' if self.peek() == '*' => {
                    self.skip();
                    depth += 1;
                }
                '*' if self.peek() == '/' => {
                    self.skip();
                    depth -= 1;

                    // we finally reached the end of the block comment, if any subsequent '*/'
                    // sequences are present after this one, they will be
                    // tokenised separately
                    if depth == 0 {
                        break;
                    }
                }
                _ => (),
            }
        }
    }

    /// Eat while the condition holds, and discard any characters that it
    /// encounters whilst eating the input, this is useful because in some
    /// cases we don't want to preserve what the token represents, such as
    /// comments or white-spaces...
    fn eat_while_and_discard(&self, mut condition: impl FnMut(char) -> bool) {
        let slice = unsafe { self.as_slice() }.chars();

        for ch in slice {
            if condition(ch) {
                self.offset.update(|x| x + ch.len_utf8());
            } else {
                break;
            }
        }
    }

    /// Eat while the condition holds, and produces a slice from where it began
    /// to eat the input and where it finished, this is sometimes beneficial
    /// as the slice doesn't have to be re-allocated as a string.
    fn eat_while_and_slice(&self, condition: impl FnMut(char) -> bool) -> &str {
        let start = self.offset.get();
        self.eat_while_and_discard(condition);
        let end = self.offset.get();

        &self.contents[start..end]
    }
}
