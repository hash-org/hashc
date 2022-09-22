//! Utilities to validate a [TreeDef] before emitting.
use crate::definitions::TreeDef;

pub(crate) fn validate_tree_def(_def: &TreeDef) -> Result<(), syn::Error> {
    // @@Enhancement: we can manually validate some aspects of the tree definition
    // (all referenced nodes exist) in order to avoid cryptic errors later.
    Ok(())
}
