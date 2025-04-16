//! Contains logic for lowering Hash IR [Statement]s into
//! the target backend IR.

use hash_ir::ir::{Statement, StatementKind};
use hash_reporting::macros::panic_on_span;
use hash_storage::store::statics::StoreId;

use super::{FnBuilder, locals::LocalRef};
use crate::traits::builder::BlockBuilderMethods;

impl<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> FnBuilder<'a, 'b, Builder> {
    /// Lower a Hash IR [Statement] into a target backend code.
    pub fn codegen_statement(&mut self, builder: &mut Builder, statement: &Statement) {
        // @@DebugInfo: deal with debug information here for the location
        // of the statement.
        match statement.kind {
            StatementKind::Assign(place, ref value) => {
                if let Some(local) = place.as_local() {
                    match self.locals[local] {
                        LocalRef::Place(destination) => {
                            self.codegen_rvalue(builder, destination, value)
                        }
                        LocalRef::Operand(None) => {
                            let operand = self.codegen_rvalue_operand(builder, value);
                            self.locals[local] = LocalRef::Operand(Some(operand));

                            // @@DebugInfo: we introduced the local here...
                        }
                        LocalRef::Operand(Some(operand)) => {
                            let is_zst = operand.info.layout.borrow().is_zst();
                            // We can't have another assignment for a local ref since
                            // this implies that it is not in SSA form (unless it is a
                            // ZST for which the rules are slightly bent). However, we
                            // must still codegen the rvalue.
                            if !is_zst {
                                panic_on_span!(
                                    statement.origin.span(),
                                    "operand `{value:?}` already has an assignment"
                                )
                            };

                            self.codegen_rvalue_operand(builder, value);
                        }
                    }
                } else {
                    // We have to emit code for computing the `place` that
                    // this specifies which will return a `destination` and then
                    // we code generate the rvalue, and store the result in the
                    // specified `destination`.

                    let destination = self.codegen_place(builder, place);
                    self.codegen_rvalue(builder, destination, value);
                }
            }
            StatementKind::Discriminate(place, discriminant) => {
                self.codegen_place(builder, place).codegen_set_discriminant(builder, discriminant);
            }
            StatementKind::Live(local) => {
                if let LocalRef::Place(place) = self.locals[local] {
                    place.storage_live(builder);
                }
            }
            StatementKind::Dead(local) => {
                if let LocalRef::Place(place) = self.locals[local] {
                    place.storage_dead(builder);
                }
            }
            StatementKind::Nop => {}
        }
    }
}
