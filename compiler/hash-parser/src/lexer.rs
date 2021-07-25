//! Hash compiler low level implementation for the language lexer. Convert
//! an arbitrary string into a sequence of Lexemes.
//!
//! All rights reserved 2021 (c) The Hash Language authors
use hash_ast::ast::AstString;
use hash_ast::ident::IDENTIFIER_MAP;
use hash_ast::location::Location;

use crate::caching::STRING_LITERAL_MAP;
use crate::token::Delimiter;
use crate::token::Token;
use crate::token::TokenError;
use crate::token::TokenErrorKind;
use crate::token::TokenKind;
use crate::token::TokenResult;
use crate::utils::*;
use std::cell::Cell;
use std::iter;

/// Representing the end of stream, or the initial character that is set as 'prev' in
/// a [Lexer] since there is no character before the start.
const EOF_CHAR: char = '\0';

pub(crate) struct Lexer<'a> {
    /// Location of the lexer in the current stream.
    offset: Cell<usize>,

    contents: &'a str,

    /// The previous character of the current stream, this is useful for keeping track
    /// of state when tokenising compound inputs that rely on previous context.
    prev: Cell<Option<char>>,
}

impl<'a> Lexer<'a> {
    /// Create a new [Lexer] from the given string input.
    pub(crate) fn new(contents: &'a str) -> Self {
        Lexer {
            offset: Cell::new(0),
            contents,
            prev: Cell::new(None),
        }
    }

    /// Returns amount of already consumed symbols.
    pub(crate) fn len_consumed(&self) -> usize {
        self.offset.get()
    }

    /// Peeks the next symbol from the input stream without consuming it.
    pub(crate) fn peek(&self) -> char {
        self.nth_char(0)
    }

    /// Peeks the second symbol from the input stream without consuming it.
    pub(crate) fn peek_second(&self) -> char {
        self.nth_char(1)
    }

    /// Returns nth character relative to the current position.
    /// If requested position doesn't exist, `EOF_CHAR` is returned.
    /// However, getting `EOF_CHAR` doesn't always mean actual end of file,
    /// it should be checked with `is_eof` method.
    fn nth_char(&self, n: usize) -> char {
        let offset = self.offset.get();

        // @@Safety: We rely that the byte offset is correctly computed when stepping over the
        //           characters in the iterator.
        let slice = unsafe { std::str::from_utf8_unchecked(&self.contents.as_bytes()[offset..]) };

        slice.chars().nth(n).unwrap_or(EOF_CHAR)
    }

    /// Moves to the next character.
    pub(crate) fn next(&self) -> Option<char> {
        let offset = self.offset.get();

        // @@Safety: We rely that the byte offset is correctly computed when stepping over the
        //           characters in the iterator.
        let slice = unsafe { std::str::from_utf8_unchecked(&self.contents.as_bytes()[offset..]) };
        let ch = slice.chars().next()?;

        // only increment the offset by one if there is a next character
        self.prev.set(Some(ch));

        self.offset.set(offset + ch.len_utf8());
        Some(ch)
    }

    /// Checks if there is nothing more to consume.
    pub(crate) fn is_eof(&self) -> bool {
        self.contents.len() == self.len_consumed()
    }

    /// Parses a token from the input string.
    pub(crate) fn advance_token(&self) -> Option<Token> {
        let offset = self.offset.get();

        // Eat any comments or whitespace before processing the token...
        loop {
            match self.peek() {
                c if c.is_whitespace() => self.eat_while_and_discard(char::is_whitespace),
                '/' => match self.peek_second() {
                    '*' => self.block_comment(),
                    '/' => self.line_comment(),
                    _ => {
                        self.next();

                        // @@Hack: since we already compare if the first item is a slash, we'll just
                        // return here the slash and advance it by one.
                        return Some(Token::new(TokenKind::Slash, Location::pos(offset)));
                    }
                },
                _ => break,
            }
        }

        // We avoid checking if the tokens are compound here because we don't really want to deal with commments
        // and spaces in an awkard way... Once the whole stream is transformed into a bunch of tokens, we can then
        // combine these tokens into more complex variants that might span multiple characters. For example, the code...
        // > ':' => match self.peek() {
        // >     ':' => {
        // >         self.next();
        // >         break TokenKind::NameAccess
        // >     }
        // >     _ => break TokenKind::Colon
        // > },
        //
        // could work here, but however what about if there was a space or a comment between the colons, this might be
        // problematic. Essentially, we pass the responsobility of forming more compound tokens to AST gen rather than here.
        let token_kind = match self.next()? {
            // One-symbol tokens
            '~' => TokenKind::Tilde,
            '=' => TokenKind::Eq,
            '!' => TokenKind::Exclamation,
            '-' => TokenKind::Minus,
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

            // Consume a token tree, which is a starting delimiter, followed by a an arbitrary number of tokens and closed
            // by a followiing delimiter...
            ch @ ('(' | '{' | '[') => self
                .eat_token_tree(Delimiter::from_left(ch).unwrap())
                .unwrap(),

            // Identifier (this should be checked after other variant that can
            // start as identifier).
            c if is_id_start(c) => self.ident(),

            // Numeric literal.
            '0'..='9' => self
                .number()
                .unwrap_or_else(|e| panic!("error: {:#?}", e.message)),

            // character literal.
            // @@ErrorReporting: this is where we hook into error reporting to print the result
            // and display it to the user
            '\'' => self
                .char()
                .unwrap_or_else(|e| panic!("error: {:#?}", e.message)),

            // String literal.
            '"' => self.string().unwrap_or_else(|e| panic!("error: {:?}", e)),

            // We have to exit the current tree if we encounter a closing delimiter...
            ')' | '}' | ']' => return None,
            _ => TokenKind::Unexpected,
        };

        let location = Location::span(offset, self.len_consumed());
        Some(Token::new(token_kind, location))
    }

    /// This will essentially recursively consume tokens until it reaches the right hand-side variant
    /// of the provided delimiter. If no delimiter is reached, but the stream has reached EOF, this is reported
    /// as an error because it is essentially an un-closed block. This kind of behaviour is desired and avoids
    /// perfoming complex delimiter depth analysis later on.
    pub(crate) fn eat_token_tree(&self, delimiter: Delimiter) -> TokenResult<TokenKind> {
        debug_assert!(self.prev.get().unwrap() == delimiter.left());

        let mut children_tokens = vec![];

        let start = self.offset.get();

        while !self.is_eof() {
            // @@ErrorReporting: Option here doesn't just mean EOF, it could also be that the next token failed to be parsed.
            match self.advance_token() {
                Some(token) => children_tokens.push(token),
                None => break,
            };
        }

        match self.prev.get().unwrap() == delimiter.right() {
            false => Err(TokenError::new(
                None,
                TokenErrorKind::Unclosed(delimiter),
                Location::pos(start),
            )),
            true => Ok(TokenKind::Tree(delimiter, children_tokens)),
        }
    }

    /// Consume an identifier, at this stage keywords are also considered to be identfiers. The function
    /// expects that the first character of the identifier is consumed when the function is called.
    pub(crate) fn ident(&self) -> TokenKind {
        let first = self.prev.get().unwrap();
        debug_assert!(is_id_start(first));

        let suffix = self.eat_while(is_id_continue);
        let name: String = iter::once(first).chain(suffix).collect();

        // create the identifier here from the created map
        let ident = IDENTIFIER_MAP.create_ident(AstString::Owned(name.as_str().to_owned()));
        TokenKind::Ident(ident)
    }

    /// Consume a number literal, either float or integer. The function expects that the first character of
    /// the numeric literal is consumed when the function is called.
    pub(crate) fn number(&self) -> TokenResult<TokenKind> {
        let prev = self.prev.get().unwrap();
        debug_assert!(('0'..='9').contains(&prev));

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
                self.next(); // accounting for the radix

                let chars = self.eat_decimal_digits(radix);
                let value = u64::from_str_radix(chars, radix);

                // @@ErrorHandling: We shouldn't error here, this should be handeled by the SmallVec<..> change to integers
                if value.is_err() {
                    return Err(TokenError::new(
                        Some("Integer literal too large".to_string()),
                        TokenErrorKind::MalformedNumericalLiteral,
                        Location::span(start, self.offset.get()),
                    ));
                }

                return Ok(TokenKind::IntLiteral(value.unwrap()));
            }
        }

        let pre_digit = self.prev.get().unwrap();
        let pre_digits = iter::once(pre_digit).chain(self.eat_decimal_digits(10).chars());

        // peek next to check if this is an actual float literal...
        match self.peek() {
            '.' => {
                // Only eat the char
                self.next();

                let after_digits = self.eat_decimal_digits(10);

                let num = pre_digits
                    .chain(std::iter::once('.'))
                    .chain(after_digits.chars());

                self.eat_float_literal(num, start)
            }
            // Imediate exponent
            'e' | 'E' => self.eat_float_literal(pre_digits, start),
            _ => match pre_digits.collect::<String>().parse::<u64>() {
                Err(_) => Err(TokenError::new(
                    Some("Integer literal too large.".to_string()),
                    TokenErrorKind::MalformedNumericalLiteral,
                    Location::span(start, self.offset.get()),
                )),
                Ok(value) => Ok(TokenKind::IntLiteral(value)),
            },
        }
    }

    /// Function to apply an exponent to a floating point literal.
    fn eat_float_literal(
        &self,
        num: impl Iterator<Item = char>,
        start: usize,
    ) -> TokenResult<TokenKind> {
        let num = num.collect::<String>().parse::<f64>();

        match num {
            Err(_) => Err(TokenError::new(
                Some("Malformed float literal.".to_string()),
                TokenErrorKind::MalformedNumericalLiteral,
                Location::span(start, self.offset.get()),
            )),
            Ok(value) => {
                let exp = self.eat_exponent()?;

                // if an exponent was speified, as in it is non-zero, we need to apply the exponent to
                // the float literal.
                let value = if exp != 0 { value * 10f64.powi(exp) } else { value };

                Ok(TokenKind::FloatLiteral(value))
            }
        }
    }

    /// Consume an exponent for a float literal.
    fn eat_exponent(&self) -> TokenResult<i32> {
        if !matches!(self.peek(), 'e' | 'E') {
            // @@Hack: we return a zero to signal that there was no exponent and therefore avoid applying it later
            return Ok(0);
        }

        self.next(); // consume the exponent

        let start = self.offset.get();

        // Check if there is a sign before the digits start in the exponent...
        let negated = if self.peek() == '-' {
            self.next();
            true
        } else {
            false
        };

        match self.eat_decimal_digits(10).parse::<i32>() {
            Err(_) => Err(TokenError::new(
                Some("Invalid float exponent.".to_string()),
                TokenErrorKind::MalformedNumericalLiteral,
                Location::span(start, self.offset.get()),
            )),
            Ok(num) if negated => Ok(-num),
            Ok(num) => Ok(num),
        }
    }

    /// Consume only decimal digits up to encountering a non-decimal digit
    /// whilst taking into account that the language supports '_' as digit
    /// separators which should just be skipped over...
    pub(crate) fn eat_decimal_digits(&self, radix: u32) -> &str {
        self.eat_while_and_slice(move |c| c.is_digit(radix) || c == '_')
    }

    /// Transform an ordinary character into a well known escape sequence specified by the
    /// escape literal rules. More information about the escape sequences can be found at
    /// [escape sequences](https://hash-org.github.io/lang/basics/intro.html)
    fn char_from_escape_seq(&self) -> TokenResult<char> {
        debug_assert!(self.prev.get().unwrap() == '\\');
        let c = self.next().unwrap();

        // we need to compute the old byte offset by accounting for both the 'u' character and the '\\' character,
        // but since this is known to be 2 bytes, we can just subtract it from the current offset
        let start = self.offset.get() - 1;

        match c {
            'n' => Ok('\n'),
            't' => Ok('\t'),
            'u' => {
                // The next character should be a '{', otherwise this isn't a correct escaped
                // literal
                if self.peek() != '{' {
                    return Err(TokenError::new(
                        Some("Expected '{' after a '\\u' escape sequence".to_string()),
                        TokenErrorKind::BadEscapeSequence,
                        Location::span(start, self.offset.get()),
                    ));
                }

                self.next();

                // here we expect up to 6 hex digits, which is finally closed by a '}'
                let chars = self.eat_while_and_slice(|c| c.is_ascii_hexdigit());

                if self.peek() != '}' {
                    return Err(TokenError::new(
                        Some("Expected '}' after a escape sequence".to_string()),
                        TokenErrorKind::BadEscapeSequence,
                        Location::span(start, self.offset.get()),
                    ));
                }
                self.next();

                let value = u32::from_str_radix(chars, 16);

                if value.is_err() {
                    return Err(TokenError::new(
                        Some("Unicode literal too long".to_string()),
                        TokenErrorKind::BadEscapeSequence,
                        Location::span(start, self.offset.get()),
                    ));
                }

                Ok(char::from_u32(value.unwrap()).unwrap())
            }
            'x' => {
                // Examples of the \x.. Escape sequence would be things like `\x07` or `\x0b`, Essentially
                // 2 hex_ascii_digits and the rest is not part of the escape sequence and can be left alone.
                let chars: Result<String, TokenError> = (0..2)
                    .map(|_| match self.peek() {
                        c if c.is_ascii_hexdigit() => Ok(self.next().unwrap()),
                        EOF_CHAR => Err(TokenError::new(
                            Some("ASCII escape code too short".to_string()),
                            TokenErrorKind::BadEscapeSequence,
                            Location::span(start, self.offset.get()),
                        )),
                        c => Err(TokenError::new(
                            Some("ASCII escape code must only contain hex digits".to_string()),
                            TokenErrorKind::Unexpected(c),
                            Location::span(start, self.offset.get()),
                        )),
                    })
                    .collect();

                let chars = chars?;

                // @@Safety: Safe to unwrap since we check that both chars are hex valid and two hex chars will
                // always to fit into a u32
                let value = u32::from_str_radix(chars.as_str(), 16).unwrap();

                Ok(char::from_u32(value).unwrap())
            }
            'a' => Ok('\x07'),
            'b' => Ok('\x08'),
            'f' => Ok('\x1b'),
            'r' => Ok('\r'),
            'v' => Ok('\x0b'),
            '\\' => Ok('\\'),
            '"' => Ok('"'),
            '\'' => Ok('\''),
            ch => Err(TokenError::new(
                Some(format!("Unknown escape sequence '{}'", ch)),
                TokenErrorKind::BadEscapeSequence,
                Location::pos(start),
            )),
        }
    }

    /// Consume a char literal provided that the current previous token is a single
    /// quote, this will produce a [TokenKind::CharLiteral] provided that the literal is
    /// correctly formed and is ended before the end of file is reached. This function expects
    /// the the callee has previously eaten the starting single quote.
    pub(crate) fn char(&self) -> TokenResult<TokenKind> {
        debug_assert!(self.prev.get().unwrap() == '\'');

        // Subtract one to capture the previous quote, since we know it's one byte in size
        let start = self.offset.get() - 1;

        // check whether the next character is a backslash, as in escaping a char, if not
        // eat the next char and expect the second character to be a "\'" char...
        if self.peek_second() == '\'' && self.peek() != '\\' {
            let ch = self.next().unwrap();
            self.next();

            return Ok(TokenKind::CharLiteral(ch));
        } else if self.peek() == '\\' {
            // otherwise, this is an escaped char and hence we eat the '\' and use the next char as
            // the actual char by escaping it
            self.next();

            let ch = self.char_from_escape_seq()?;
            let next = self.peek();

            // eat the single qoute after the character
            if next != '\'' {
                // @@Improvement: Maybe make this a function to check if we're about to hit the end...
                if next == EOF_CHAR {
                    return Err(TokenError::new(
                        Some("Unclosed character literal.".to_string()),
                        TokenErrorKind::Expected(TokenKind::SingleQoute),
                        Location::pos(self.offset.get()),
                    ));
                }

                return Err(TokenError::new(
                    Some("Character literal can only contain one codepoint.".to_string()),
                    TokenErrorKind::BadEscapeSequence,
                    Location::span(start, self.offset.get()),
                ));
            }

            self.next();

            return Ok(TokenKind::CharLiteral(ch));
        }

        Err(TokenError::new(
            None,
            TokenErrorKind::Unexpected(self.peek()),
            Location::pos(self.offset.get()),
        ))
    }

    /// Consume a string literal provided that the current previous token is a double
    /// quote, this will produce a [TokenKind::StrLiteral] provided that the literal is
    /// correctly formed and is ended before the end of file is reached.
    pub(crate) fn string(&self) -> TokenResult<TokenKind> {
        debug_assert!(self.prev.get().unwrap() == '"');

        let mut value = String::from("");

        while let Some(c) = self.next() {
            match c {
                '"' => break,
                '\\' => {
                    let ch = self.char_from_escape_seq()?;
                    value.push(ch);
                }
                ch => value.push(ch),
            }
        }

        // Essentially we put the string into the literal map and get an id out which we use for the
        // actual representation in the token
        let id = STRING_LITERAL_MAP.create_string(AstString::Owned(value));
        Ok(TokenKind::StrLiteral(id))
    }

    /// Consume a line comment after the first folloing slash, essentially eating
    /// characters up to the next '\n' encountered. If we reach EOF before a newline, then
    /// we stop eating there.
    //@@DocSupport: These could return a TokenKind so that we can feed it into some kind of documentation generator tool
    pub(crate) fn line_comment(&self) {
        debug_assert!(self.peek() == '/' && self.peek_second() == '/');
        self.next();
        self.eat_while_and_discard(|c| c != '\n');
    }

    /// Consume a block comment after the first following '/*' sequence of characters. If the
    /// iterator encounters the start of another block comment, we increment a nested comment
    /// counter to ensure that nested block comments are accounted for and handeled gracefully.
    //@@DocSupport: These could return a TokenKind so that we can feed it into some kind of documentation generator tool
    pub(crate) fn block_comment(&self) {
        debug_assert!(self.peek() == '/' && self.peek_second() == '*');
        self.next();

        // since we aren't as dumb as C++, we want to count the depth of block comments
        // and account for nested ones, we keep track of it whilst consuming the block...
        let mut depth: u32 = 1;

        while let Some(c) = self.next() {
            match c {
                '/' if self.peek() == '*' => {
                    self.next();
                    depth += 1;
                }
                '*' if self.peek() == '/' => {
                    self.next();
                    depth -= 1;

                    // we finally reached the end of the block comment, if any subsequent '*/' sequences
                    // are present after this one, they will be tokenised seperately
                    if depth == 0 {
                        break;
                    }
                }
                _ => (),
            }
        }
    }

    /// Simplified version of [`Self::eat_while()`] since this function will discard
    /// any characters that it encounters whilst eating the input, this is useful
    /// because in some cases we don't want to preserve what the token represents,
    /// such as comments or whitespaces...
    fn eat_while_and_discard(&self, mut condition: impl FnMut(char) -> bool) {
        while condition(self.peek()) && !self.is_eof() {
            self.next();
        }
    }

    /// Cousin of [Self::eat_while], it consumes the input, and produces a slice from where it began
    /// to eat the input and where it finished, this is sometimes beneficial as the slice doesn't have
    /// to be re-allocated as a string.
    fn eat_while_and_slice(&self, mut condition: impl FnMut(char) -> bool) -> &str {
        let start = self.offset.get();
        while condition(self.peek()) && !self.is_eof() {
            self.next();
        }
        let end = self.offset.get();

        &self.contents[start..end]
    }

    /// Iterator that will collect characters until a given predicate no longer passes.
    /// The function will increment the current stream position and collect characters on the
    /// way, returning an iterator so as to avoid allocating a string.
    fn eat_while<'cond>(
        &'a self,
        mut condition: impl FnMut(char) -> bool + 'cond + 'a,
    ) -> impl Iterator<Item = char> + 'cond + 'a
    where
        'a: 'cond,
    {
        std::iter::from_fn(move || {
            if condition(self.peek()) && !self.is_eof() {
                return self.next();
            }

            None
        })
    }
}

/// Function to tokenise an input string. Resulting in an iterator of [Token]s
pub fn tokenise(input: &str) -> impl Iterator<Item = Token> + '_ {
    let lexer = Lexer::new(input);

    std::iter::from_fn(move || {
        if input.is_empty() {
            return None;
        }

        lexer.advance_token()
    })
}
