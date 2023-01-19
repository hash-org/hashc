//! Utilities related to value/type coercion in the language.

use hash_ast::ast::{self, AstNodeRef};
use hash_types::terms::TermId;

use crate::{
    ops::AccessToOps,
    storage::{AccessToStorage, StorageRef},
};

pub struct Coercing<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for Coercing<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> Coercing<'tc> {
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Potentially coerce the given term to be used in value position, which
    /// originates from the given originating expression node.
    pub fn potentially_coerce_as_value(
        &self,
        term_id: TermId,
        originating_node: AstNodeRef<ast::Expr>,
    ) -> TermId {
        self.coerce_as_value(term_id, originating_node).unwrap_or(term_id)
    }

    /// Coerce the given term to be used in value position, which originates
    /// from the given originating expression node.
    ///
    /// Returns `None` if no coercion occurred.
    pub fn coerce_as_value(
        &self,
        term_id: TermId,
        originating_node: AstNodeRef<ast::Expr>,
    ) -> Option<TermId> {
        // @@Future: Currently the only purpose of this function is to coerce
        // unit types into unit values, but in the future it can be used to wrap
        // union members with a discriminant (e.g. when assigning A to A | B).

        if let (Some(nominal_def_id), true) =
            (self.oracle().term_as_nominal_def_id(term_id), self.oracle().term_is_unit_def(term_id))
        {
            if let ast::Expr::Cast(_) = originating_node.body() {
                // We don't want to do this if the unit expression is directly cast as a type
                None
            } else {
                Some(self.builder().create_unit_term(nominal_def_id))
            }
        } else {
            None
        }
    }
}
