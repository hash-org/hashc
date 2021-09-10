#![allow(dead_code)]
use hash_ast::{keyword::Keyword, resolve::ModuleResolver};

use crate::{
    gen::AstGen,
    token::{TokenAtom, TokenKind},
};

#[derive(Debug, Clone)]
pub enum Operator {
    EqEq,
    NotEq,
    BitOr,
    Or,
    BitAnd,
    And,
    BitXor,
    Exp,
    Gt,
    GtEq,
    Lt,
    LtEq,
    Shr,
    Shl,
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // @@Cleanup: This is a special operator since it performs a higher order operation compared
    //            to all other members of the Operator enum, maybe it should be in it's own enum??
    As,
}

impl Operator {
    /// This function is used to pickup 'glued' operator tokens to form more complex binary operators
    /// that might be made up of multiple tokens. The function will peek ahead (2 tokens at most since
    /// all binary operators are made of that many tokens). The function returns an optional derived
    /// operator, and the number of tokens that was consumed deriving the operator, it is the responsibility
    /// of the caller to increment the token stream by the provided number.
    pub(crate) fn from_token_stream<R: ModuleResolver>(gen: &AstGen<R>) -> (Option<Operator>, u8) {
        let token = gen.peek();

        // check if there is a token that we can peek at ahead...
        if token.is_none() {
            return (None, 0);
        }

        match &(token.unwrap()).kind {
            TokenKind::Atom(atom) => {
                match atom {
                    // Since the 'as' keyword is also a binary operator, we have to handle it here...
                    TokenAtom::Keyword(Keyword::As) => (Some(Operator::As), 1),
                    TokenAtom::Eq => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Eq) => {
                            (Some(Operator::EqEq), 2)
                        }
                        _ => (None, 0),
                    },
                    TokenAtom::Lt => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Eq) => {
                            (Some(Operator::LtEq), 2)
                        }
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Lt) => {
                            (Some(Operator::Shl), 2)
                        }
                        _ => (Some(Operator::Lt), 1),
                    },
                    TokenAtom::Gt => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Eq) => {
                            (Some(Operator::GtEq), 2)
                        }
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Gt) => {
                            (Some(Operator::Shr), 2)
                        }
                        _ => (Some(Operator::Gt), 1),
                    },
                    TokenAtom::Plus => (Some(Operator::Add), 1),
                    TokenAtom::Minus => (Some(Operator::Sub), 1),
                    TokenAtom::Star => (Some(Operator::Mul), 1),
                    TokenAtom::Slash => (Some(Operator::Div), 1),
                    TokenAtom::Percent => (Some(Operator::Mod), 1),
                    TokenAtom::Caret => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Caret) => {
                            (Some(Operator::Exp), 2)
                        }
                        _ => (Some(Operator::BitXor), 1),
                    },
                    TokenAtom::Amp => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Amp) => {
                            (Some(Operator::And), 2)
                        }
                        _ => (Some(Operator::BitAnd), 1),
                    },
                    TokenAtom::Pipe => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Pipe) => {
                            (Some(Operator::Or), 2)
                        }
                        _ => (Some(Operator::BitOr), 1),
                    },
                    TokenAtom::Exclamation => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Eq) => {
                            (Some(Operator::NotEq), 2)
                        }
                        _ => (None, 0), // this is a unary operator '!'
                    },
                    _ => (None, 0),
                }
            }
            _ => (None, 0),
        }
    }

    pub fn as_str(&self) -> &str {
        match self {
            Operator::EqEq => "eq",
            Operator::NotEq => "neq",
            Operator::BitOr => "bit_or",
            Operator::Or => "orl",
            Operator::BitAnd => "bit_and",
            Operator::And => "and",
            Operator::BitXor => "bit_xor",
            Operator::Exp => "exp",
            Operator::Gt => "gt",
            Operator::GtEq => "gt_eq",
            Operator::Lt => "lt",
            Operator::LtEq => "lt_eq",
            Operator::Shr => "shr",
            Operator::Shl => "shl",
            Operator::Add => "add",
            Operator::Sub => "sub",
            Operator::Mul => "mul",
            Operator::Div => "div",
            Operator::Mod => "mod",
            Operator::As => "as",
        }
    }

    /// Compute the precedence for an operator
    pub(crate) fn infix_binding_power(&self) -> (u8, u8) {
        match self {
            Operator::Or => (2, 3),
            Operator::And => (4, 5),
            Operator::EqEq | Operator::NotEq => (6, 5),
            Operator::Gt | Operator::GtEq | Operator::Lt | Operator::LtEq => (7, 8),
            Operator::BitOr | Operator::BitXor => (9, 10),
            Operator::BitAnd => (11, 12),
            Operator::Shr | Operator::Shl => (13, 14),
            Operator::Add | Operator::Sub => (15, 16),
            Operator::Mul | Operator::Div | Operator::Mod => (17, 18),
            Operator::Exp => (20, 19),
            Operator::As => (21, 22),
        }
    }
}

pub enum CompoundFn {
    Leq,
    Geq,
    Lt,
    Gt,
}

pub enum OperatorFn {
    Named { name: &'static str, assigning: bool },
    LazyNamed { name: &'static str, assigning: bool },
    Compound { name: CompoundFn, assigning: bool },
}

/// Function to convert a pest rule denoting operators into a named function symbols
/// that represent their function call, more details about names of functions is
/// accessible in the docs at "https://hash-org.github.io/lang/basics/operators.html"
impl OperatorFn {}
