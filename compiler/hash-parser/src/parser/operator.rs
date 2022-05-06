use hash_ast::ast::*;
use hash_ast::operator::{Operator, OperatorKind};
use hash_token::{keyword::Keyword, TokenKind};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'c, 'stream, 'resolver> AstGen<'c, 'stream, 'resolver> {
    /// This function is used to pickup 'glued' operator tokens to form more complex binary operators
    /// that might be made up of multiple tokens. The function will peek ahead (2 tokens at most since
    /// all binary operators are made of that many tokens). The function returns an optional derived
    /// operator, and the number of tokens that was consumed deriving the operator, it is the responsibility
    /// of the caller to increment the token stream by the provided number.
    pub(crate) fn parse_operator(&self) -> (Option<Operator>, u8) {
        let token = self.peek();

        // check if there is a token that we can peek at ahead...
        if token.is_none() {
            return (None, 0);
        }

        let (op, mut consumed): (_, u8) = match &(token.unwrap()).kind {
            // Since the 'as' keyword is also a binary operator, we have to handle it here...
            TokenKind::Keyword(Keyword::As) => (Some(OperatorKind::As), 1),
            TokenKind::Eq => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(OperatorKind::EqEq), 2),
                _ => (None, 0),
            },
            TokenKind::Lt => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(OperatorKind::LtEq), 2),
                Some(token) if token.kind == TokenKind::Lt => (Some(OperatorKind::Shl), 2),
                _ => (Some(OperatorKind::Lt), 1),
            },
            TokenKind::Gt => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(OperatorKind::GtEq), 2),
                Some(token) if token.kind == TokenKind::Gt => (Some(OperatorKind::Shr), 2),
                _ => (Some(OperatorKind::Gt), 1),
            },
            TokenKind::Plus => (Some(OperatorKind::Add), 1),
            TokenKind::Minus => (Some(OperatorKind::Sub), 1),
            TokenKind::Star => (Some(OperatorKind::Mul), 1),
            TokenKind::Slash => (Some(OperatorKind::Div), 1),
            TokenKind::Percent => (Some(OperatorKind::Mod), 1),
            TokenKind::Caret => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Caret => (Some(OperatorKind::Exp), 2),
                _ => (Some(OperatorKind::BitXor), 1),
            },
            TokenKind::Amp => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Amp => (Some(OperatorKind::And), 2),
                _ => (Some(OperatorKind::BitAnd), 1),
            },
            TokenKind::Pipe => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Pipe => (Some(OperatorKind::Or), 2),
                _ => (Some(OperatorKind::BitOr), 1),
            },
            TokenKind::Exclamation => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(OperatorKind::NotEq), 2),
                _ => (None, 0), // this is a unary operator '!'
            },
            _ => (None, 0),
        };

        match op {
            // check if the operator is re-assignable and if so try to parse a equality operator.
            // If we see this one then we can parse and then just convert the operator into the
            // 'Eq' version.
            Some(kind) => {
                let assigning = match self.peek_nth(consumed as usize) {
                    Some(token) if kind.is_re_assignable() && token.has_kind(TokenKind::Eq) => {
                        consumed += 1;
                        true
                    }
                    _ => false,
                };

                (Some(Operator { kind, assigning }), consumed)
            }
            None => (None, 0),
        }
    }

    /// This will parse an operator and check that it is re-assignable, if the operator is not
    /// re-assignable then the result of the function is an [AstGenError] since it expects there
    /// to be this operator.
    pub(crate) fn parse_re_assignment_op(&self) -> AstGenResult<'c, AstNode<'c, Operator>> {
        let start = self.next_location();
        let (operator, consumed_tokens) = self.parse_operator();

        match operator {
            Some(Operator {
                kind,
                assigning: true,
            }) => {
                // consume the number of tokens eaten whilst getting the operator...
                self.offset.update(|x| x + consumed_tokens as usize);

                Ok(self.node_with_joined_location(
                    Operator {
                        kind,
                        assigning: true,
                    },
                    &start,
                ))
            }
            _ => self.error(AstGenErrorKind::ReAssignmentOp, None, None), // TODO: actually add information here
        }
    }

    /// Function to parse a fat arrow component '=>' in any given context.
    pub(crate) fn parse_arrow(&self) -> AstGenResult<'c, ()> {
        // Essentially, we want to re-map the error into a more concise one given
        // the parsing context.
        if self.parse_token_atom(TokenKind::Eq).is_err() {
            return self.error(AstGenErrorKind::ExpectedArrow, None, None)?;
        }

        if self.parse_token_atom(TokenKind::Gt).is_err() {
            return self.error(AstGenErrorKind::ExpectedArrow, None, None)?;
        }

        Ok(())
    }

    /// Function to parse a fat arrow component '=>' in any given context.
    pub(crate) fn parse_thin_arrow(&self) -> AstGenResult<'c, ()> {
        // Essentially, we want to re-map the error into a more concise one given
        // the parsing context.
        if self.parse_token_atom(TokenKind::Minus).is_err() {
            return self.error(AstGenErrorKind::ExpectedFnArrow, None, None)?;
        }

        if self.parse_token_atom(TokenKind::Gt).is_err() {
            return self.error(AstGenErrorKind::ExpectedFnArrow, None, None)?;
        }

        Ok(())
    }
}
