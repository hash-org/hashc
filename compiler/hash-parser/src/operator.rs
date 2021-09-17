use hash_ast::{keyword::Keyword, resolve::ModuleResolver};

use crate::{
    gen::AstGen,
    token::{TokenAtom, TokenKind},
};

#[derive(Debug, Clone)]
pub struct Operator {
    pub kind: OperatorKind,
    pub assignable: bool,
}

#[derive(Debug, Clone)]
pub enum OperatorKind {
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

        let (op, mut consumed): (_, u8) = match &(token.unwrap()).kind {
            TokenKind::Atom(atom) => {
                match atom {
                    // Since the 'as' keyword is also a binary operator, we have to handle it here...
                    TokenAtom::Keyword(Keyword::As) => (Some(OperatorKind::As), 1),
                    TokenAtom::Eq => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Eq) => {
                            (Some(OperatorKind::EqEq), 2)
                        }
                        _ => (None, 0),
                    },
                    TokenAtom::Lt => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Eq) => {
                            (Some(OperatorKind::LtEq), 2)
                        }
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Lt) => {
                            (Some(OperatorKind::Shl), 2)
                        }
                        _ => (Some(OperatorKind::Lt), 1),
                    },
                    TokenAtom::Gt => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Eq) => {
                            (Some(OperatorKind::GtEq), 2)
                        }
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Gt) => {
                            (Some(OperatorKind::Shr), 2)
                        }
                        _ => (Some(OperatorKind::Gt), 1),
                    },
                    TokenAtom::Plus => (Some(OperatorKind::Add), 1),
                    TokenAtom::Minus => (Some(OperatorKind::Sub), 1),
                    TokenAtom::Star => (Some(OperatorKind::Mul), 1),
                    TokenAtom::Slash => (Some(OperatorKind::Div), 1),
                    TokenAtom::Percent => (Some(OperatorKind::Mod), 1),
                    TokenAtom::Caret => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Caret) => {
                            (Some(OperatorKind::Exp), 2)
                        }
                        _ => (Some(OperatorKind::BitXor), 1),
                    },
                    TokenAtom::Amp => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Amp) => {
                            (Some(OperatorKind::And), 2)
                        }
                        _ => (Some(OperatorKind::BitAnd), 1),
                    },
                    TokenAtom::Pipe => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Pipe) => {
                            (Some(OperatorKind::Or), 2)
                        }
                        _ => (Some(OperatorKind::BitOr), 1),
                    },
                    TokenAtom::Exclamation => match gen.peek_second() {
                        Some(token) if token.kind == TokenKind::Atom(TokenAtom::Eq) => {
                            (Some(OperatorKind::NotEq), 2)
                        }
                        _ => (None, 0), // this is a unary operator '!'
                    },
                    _ => (None, 0),
                }
            }
            _ => (None, 0),
        };

        match op {
            // check if the operator is re-assignable and if so try to parse a equality operator.
            // If we see this one then we can parse and then just convert the operator into the
            // 'Eq' version.
            Some(kind) => {
                let assignable = match gen.peek_nth(consumed as usize) {
                    Some(token) if kind.is_re_assignable() && token.has_atom(TokenAtom::Eq) => {
                        consumed += 1;
                        true
                    }
                    _ => false,
                };

                (Some(Operator { kind, assignable }), consumed)
            }
            None => (None, 0),
        }
    }
}

impl std::fmt::Display for OperatorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OperatorKind::EqEq => write!(f, "=="),
            OperatorKind::NotEq => write!(f, "!="),
            OperatorKind::BitOr => write!(f, "|"),
            OperatorKind::Or => write!(f, "||"),
            OperatorKind::BitAnd => write!(f, "&"),
            OperatorKind::And => write!(f, "&&"),
            OperatorKind::BitXor => write!(f, "^"),
            OperatorKind::Exp => write!(f, "^^"),
            OperatorKind::Gt => write!(f, ">"),
            OperatorKind::GtEq => write!(f, ">="),
            OperatorKind::Lt => write!(f, "<"),
            OperatorKind::LtEq => write!(f, "<="),
            OperatorKind::Shr => write!(f, "<<"),
            OperatorKind::Shl => write!(f, ">>"),
            OperatorKind::Add => write!(f, "+"),
            OperatorKind::Sub => write!(f, "-"),
            OperatorKind::Mul => write!(f, "*"),
            OperatorKind::Div => write!(f, "/"),
            OperatorKind::Mod => write!(f, "%"),
            OperatorKind::As => write!(f, "as"),
        }
    }
}

impl OperatorKind {
    /// This returns if an operator is actually re-assignable. By re-assignable, this is in the sense
    /// that you can add a '=' to mean that you are performing a re-assigning operation using the left
    /// hand-side expression as a starting point and the rhs as the other argument to the operator.
    /// For example, `a += b` is re-assigning because it means `a = a + b`.
    pub(crate) fn is_re_assignable(&self) -> bool {
        matches!(
            self,
            OperatorKind::BitOr
                | OperatorKind::Or
                | OperatorKind::BitAnd
                | OperatorKind::And
                | OperatorKind::BitXor
                | OperatorKind::Exp
                | OperatorKind::Shr
                | OperatorKind::Shl
                | OperatorKind::Add
                | OperatorKind::Sub
                | OperatorKind::Mul
                | OperatorKind::Div
                | OperatorKind::Mod
        )
    }

    pub fn as_str(&self) -> &str {
        match self {
            OperatorKind::EqEq => "eq",
            OperatorKind::NotEq => "neq",
            OperatorKind::BitOr => "bit_or",
            OperatorKind::Or => "orl",
            OperatorKind::BitAnd => "bit_and",
            OperatorKind::And => "and",
            OperatorKind::BitXor => "bit_xor",
            OperatorKind::Exp => "exp",
            OperatorKind::Gt => "gt",
            OperatorKind::GtEq => "gt_eq",
            OperatorKind::Lt => "lt",
            OperatorKind::LtEq => "lt_eq",
            OperatorKind::Shr => "shr",
            OperatorKind::Shl => "shl",
            OperatorKind::Add => "add",
            OperatorKind::Sub => "sub",
            OperatorKind::Mul => "mul",
            OperatorKind::Div => "div",
            OperatorKind::Mod => "mod",
            OperatorKind::As => "as",
        }
    }

    /// Compute the precedence for an operator
    pub(crate) fn infix_binding_power(&self) -> (u8, u8) {
        match self {
            OperatorKind::Or => (2, 3),
            OperatorKind::And => (4, 5),
            OperatorKind::EqEq | OperatorKind::NotEq => (6, 5),
            OperatorKind::Gt | OperatorKind::GtEq | OperatorKind::Lt | OperatorKind::LtEq => (7, 8),
            OperatorKind::BitOr | OperatorKind::BitXor => (9, 10),
            OperatorKind::BitAnd => (11, 12),
            OperatorKind::Shr | OperatorKind::Shl => (13, 14),
            OperatorKind::Add | OperatorKind::Sub => (15, 16),
            OperatorKind::Mul | OperatorKind::Div | OperatorKind::Mod => (17, 18),
            OperatorKind::Exp => (20, 19),
            OperatorKind::As => (21, 22),
        }
    }
}
