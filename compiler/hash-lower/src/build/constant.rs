//! Utilities and operations that involve [Const]s when lowering expressions.
//! This module also includes logic that can perform constant folding on
//! various constants.

use hash_ir::ir;
use hash_reporting::macros::panic_on_span;
use hash_storage::store::statics::StoreId;
use hash_tir::tir::{self, HasAstNodeId};

use super::BodyBuilder;

impl<'tcx> BodyBuilder<'tcx> {
    /// Lower a literal value into a [constant::Const].
    pub(crate) fn lit_as_const(&self, lit: tir::LitId) -> ir::Const {
        match *lit.value() {
            tir::Lit::Int(_) | tir::Lit::Float(_) => {
                panic!("unbakend float/integer literal in IR")
            }
            tir::Lit::Const(constant) => constant,
        }
    }

    /// Lower a constant expression, i.e. a literal value.
    #[allow(unused)]
    pub(crate) fn lower_const_term(&mut self, term: tir::TermId) -> ir::Const {
        // @@TirToConst: implement the conversion from an arbitrary TIR data term into a
        // Const value.
        match *term.value() {
            tir::Term::Lit(lit) => self.lit_as_const(lit),
            tir::Term::Array(_arr) => {
                unimplemented!("lowering of constant Array terms is not yet implemented")
            }
            tir::Term::Tuple(_tup) => {
                unimplemented!("lowering of constant Tuple terms is not yet implemented")
            }
            tir::Term::Ctor(_ctor) => {
                unimplemented!("lowering of constant Ctor terms is not yet implemented")
            }
            _ => panic_on_span!(
                term.span().unwrap(),
                "cannot lower non-constant expression into constant"
            ),
        }
    }
}
