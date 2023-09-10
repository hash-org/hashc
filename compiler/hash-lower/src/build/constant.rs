//! Utilities and operations that involve [Const]s when lowering expressions.
//! This module also includes logic that can perform constant folding on
//! various constants.

use hash_ast::ast::AstNodeId;
use hash_ir::{constant, constant::ConstKind, ir, ty::IrTyId};
use hash_reporting::macros::panic_on_span;
use hash_storage::store::statics::StoreId;
use hash_tir::{
    lits::{Lit, LitId},
    node::{HasAstNodeId, Node},
    terms::Term,
};

use super::BodyBuilder;

/// Convert a [LitId] into an [ir::Const].
#[inline]
pub fn lit_to_const(lit: LitId) -> ir::Const {
    match *lit.value() {
        Lit::Int(lit) => ir::Const::Int(lit.interned_value()),
        Lit::Str(lit) => ir::Const::Str(lit.interned_value()),
        Lit::Char(lit) => ir::Const::Char(lit.value()),
        Lit::Float(lit) => ir::Const::Float(lit.interned_value()),
    }
}

impl<'tcx> BodyBuilder<'tcx> {
    /// Lower a simple literal into an [ir::Const], this does not deal
    /// with literals that are arrays or other compound data structures.
    pub(crate) fn as_constant(&mut self, lit: LitId) -> ir::Const {
        lit_to_const(lit)
    }

    /// Lower a constant expression, i.e. a literal value.
    pub(crate) fn lower_constant_expr(&mut self, term: &Term, origin: AstNodeId) -> ir::Const {
        match term {
            Term::Lit(lit) => self.as_constant(*lit),
            // @@TirToConst: implement the conversion from an arbitrary TIR data term into a Const
            // value.
            _ => panic_on_span!(origin.span(), "cannot lower non-literal expression into constant"),
        }
    }

    /// Lower a literal value into a [constant::Const].
    #[allow(unused)]
    pub(crate) fn lit_as_const(&mut self, lit: LitId, ty: IrTyId) -> constant::Const {
        constant::Const::new(ty, ConstKind::from_lit(*lit.value(), &self.ctx))
    }

    /// Lower a constant expression, i.e. a literal value.
    #[allow(unused)]
    pub(crate) fn lower_const_term(&mut self, term: &Node<Term>, ty: IrTyId) -> constant::Const {
        // @@TirToConst: implement the conversion from an arbitrary TIR data term into a
        // Const value.

        match term.data {
            Term::Lit(lit) => self.lit_as_const(lit, ty),
            Term::Array(_arr) => {
                unimplemented!("lowering of constant Array terms is not yet implemented")
            }
            Term::Tuple(_tup) => {
                unimplemented!("lowering of constant Tuple terms is not yet implemented")
            }
            Term::Ctor(_ctor) => {
                unimplemented!("lowering of constant Ctor terms is not yet implemented")
            }
            _ => panic_on_span!(
                term.span().unwrap(),
                "cannot lower non-constant expression into constant"
            ),
        }
    }
}
