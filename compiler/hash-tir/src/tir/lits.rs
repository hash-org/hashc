//! Contains structures related to literals, like numbers, strings, etc.
use std::{fmt::Display, ops::Deref};

use hash_ast::ast;
use hash_ast_utils::lit::{parse_float_const_from_lit, parse_int_const_from_lit, LitParseResult};
use hash_const_eval::{print::ScalarPrinter, Const, ConstKind};
use hash_source::Size;
use hash_storage::store::statics::StoreId;
use hash_target::{
    primitives::{FloatTy, IntTy},
    HasTarget,
};

use crate::{stores::tir_stores, tir_node_single_store};

/// A literal
#[derive(Copy, Clone, Debug)]
pub enum Lit {
    /// An integer literal that is unbaked, it will require conversion into a
    /// [`Lit::Const`].
    Int(ast::IntLit),
    /// A float literal that is unbaked, it will require conversion into a
    /// [`Lit::Const`].
    Float(ast::FloatLit),

    /// A constant value that has been either baked or directly written.
    Const(Const),
}

tir_node_single_store!(Lit);

impl Lit {
    /// Bakes the integer literal into a known representation.
    ///
    /// This function does not do anything if the literal has already been
    /// baked.
    ///
    /// @@Future: we shouldn't change the literal in-place, we should return a
    /// new literal value, or we should return a new term which is the bigint
    /// term.
    pub fn bake_int<E: HasTarget>(&mut self, env: &E, annotation: IntTy) -> LitParseResult<()> {
        if let Lit::Int(lit) = self {
            let value =
                parse_int_const_from_lit(lit, Some(annotation), env.target().ptr_size(), true)?;
            *self = Lit::Const(value);
        }

        Ok(())
    }

    /// Bakes the float literal into a known representation.
    ///
    /// This function does not do anyttihng if the literal has already been
    /// baked.
    pub fn bake_float(&mut self, float_ty: FloatTy) -> LitParseResult<()> {
        if let Lit::Float(lit) = self {
            let value = parse_float_const_from_lit(lit, Some(float_ty))?;
            *self = Lit::Const(value);
        }

        Ok(())
    }
}

/// A literal pattern
///
/// This is a literal that can appear in a pattern, which does not include
/// floats.
#[derive(Copy, Clone, Debug)]
pub struct LitPat(pub LitId);

impl Deref for LitPat {
    type Target = LitId;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Display for LitPat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", *self.0.value())
    }
}

impl Display for Lit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Lit::Int(_) | Lit::Float(_) => write!(f, "<raw>"),

            // @@Fugly: we should use `ConstWriter` here (especially when it becomes
            // `Term::Const`)
            Lit::Const(constant) => {
                // It's often the case that users don't include the range of the entire
                // integer and so we will write `-2147483648..x` and
                // same for max, what we want to do is write `MIN`
                // and `MAX` for these situations since it is easier for the
                // user to understand the problem.
                let ty = constant.ty().value();

                match constant.kind {
                    ConstKind::Zero => write!(f, "()"),
                    ConstKind::Scalar(scalar) => {
                        write!(f, "{}", ScalarPrinter::new(scalar, &ty, Size::from_bits(64), true))
                    }
                    ConstKind::Pair { data, .. } if ty.is_str() => {
                        write!(f, "\"{}\"", data.to_str())
                    }
                    ConstKind::Pair { .. } => {
                        write!(f, "OPAQUE(pair)")
                    }
                    ConstKind::Alloc { .. } => {
                        // @@Todo: fixme
                        write!(f, "OPAQUE(alloc)")
                    }
                }
            }
        }
    }
}

impl Display for LitId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", *self.value())
    }
}
