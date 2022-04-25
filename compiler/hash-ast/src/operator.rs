//! Hash compiler AST operator abstract representations.
//!
//! All rights reserved 2022 (c) The Hash Language authors

/// Struct representing an operator with a kind and a flag
/// denoting whether the operator is re-assigning the left
/// hand side expression.
#[derive(Debug, Clone)]
pub struct Operator {
    /// The kind of operator.
    pub kind: OperatorKind,
    /// Flag representing where the operator is re-assigning or not.
    pub assigning: bool,
}

/// This implementation will be used for printing code from tokens.
impl std::fmt::Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.assigning {
            true => write!(f, "{}=", self.kind),
            false => write!(f, "{}", self.kind),
        }
    }
}

impl Operator {
    pub fn to_str(&self) -> &'static str {
        if self.assigning && self.kind.is_re_assignable() {
            match self.kind {
                OperatorKind::BitOr => "orb_eq",
                OperatorKind::Or => "or_eq",
                OperatorKind::BitAnd => "andb_eq",
                OperatorKind::And => "and_eq",
                OperatorKind::BitXor => "xorb_eq",
                OperatorKind::Exp => "exp_eq",
                OperatorKind::Shr => "shr_eq",
                OperatorKind::Shl => "shl_eq",
                OperatorKind::Add => "add_eq",
                OperatorKind::Sub => "sub_eq",
                OperatorKind::Mul => "mul_eq",
                OperatorKind::Div => "div_eq",
                OperatorKind::Mod => "mod_eq",
                _ => unreachable!(),
            }
        } else {
            self.kind.to_str()
        }
    }
}

#[derive(Debug, Clone, Copy)]
/// The operator kind enumeration. This represents all types of
/// operator present in the language.
pub enum OperatorKind {
    /// '=='
    EqEq,
    /// '!='
    NotEq,
    /// '|'
    BitOr,
    /// '||'
    Or,
    /// '&'
    BitAnd,
    /// '&&'
    And,
    /// '^'
    BitXor,
    /// '^^'
    Exp,
    /// '>'
    Gt,
    /// '>='
    GtEq,
    /// '<'
    Lt,
    /// '<='
    LtEq,
    /// '>>'
    Shr,
    /// '<<'
    Shl,
    /// '+'
    Add,
    /// '-'
    Sub,
    /// '*'
    Mul,
    /// '/'
    Div,
    /// '%'
    Mod,
    /// 'as'
    As,
}

/// This implementation will be used for printing code from tokens.
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
    pub fn is_re_assignable(&self) -> bool {
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

    /// operators exhibit short circuiting behaviour.
    pub fn is_lazy(&self) -> bool {
        matches!(self, OperatorKind::And | OperatorKind::Or,)
    }

    /// Compound functions that use multiple function calls when they are transformed.
    pub fn is_compound(&self) -> bool {
        matches!(
            self,
            OperatorKind::Lt | OperatorKind::Gt | OperatorKind::LtEq | OperatorKind::GtEq
        )
    }

    pub fn to_str(&self) -> &'static str {
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
    pub fn infix_binding_power(&self) -> (u8, u8) {
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
