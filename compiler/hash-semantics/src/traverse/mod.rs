//! Contains functions to traverse and typecheck the AST.

use self::coerce::Coercing;
use crate::storage::AccessToStorage;

pub mod coerce;
pub(crate) mod operators;
pub mod params;
pub mod scopes;
pub mod visitor;

/// Trait to access various structures that can perform traversal related
/// operations by a reference to a [StorageRef](crate::storage::StorageRef).
pub trait AccessToTraverseOps: AccessToStorage {
    /// Create an instance of [Coercing].
    fn coercing(&self) -> Coercing {
        Coercing::new(self.storages())
    }
}

impl<T: AccessToStorage> AccessToTraverseOps for T {}
