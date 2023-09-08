//! Utilities and operations that involve [Const]s when lowering expressions.
//! This module also includes logic that can perform constant folding on
//! various constants.

use hash_ast::ast::AstNodeId;
use hash_ir::ir;
use hash_reporting::macros::panic_on_span;
use hash_storage::store::statics::StoreId;
use hash_tir::{
    lits::{Lit, LitId},
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
}
