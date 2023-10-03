//! Utilities for dumping the TIR during typechecking.

use hash_attrs::{attr::attr_store, builtin::attrs};
use hash_tir::{dump::dump_tir, tir::HasAstNodeId};

/// Dump the TIR for the given target if it has a `#dump_tir` directive
/// applied on it.
pub fn potentially_dump_tir(target: impl ToString + HasAstNodeId) {
    let has_dump_dir = if let Some(id) = target.node_id() {
        attr_store().node_has_attr(id, attrs::DUMP_TIR)
    } else {
        false
    };

    if has_dump_dir {
        dump_tir(target);
    }
}
