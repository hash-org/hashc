//! Contains structures to keep track of traits and information relating to
//! them.
use std::fmt;

use hash_source::identifier::Identifier;
use hash_utils::{new_store, new_store_key, store::CloneStore};

use crate::{
    fmt::{ForFormatting, PrepareForFormatting},
    scope::ScopeId,
};

/// A trait definition, containing a binding name and a set of constant members.
#[derive(Debug, Clone, Copy)]
pub struct TrtDef {
    pub name: Option<Identifier>,
    pub members: ScopeId,
}

new_store_key!(pub TrtDefId);
new_store!(pub TrtDefStore<TrtDefId, TrtDef>);

impl PrepareForFormatting for TrtDefId {}

impl fmt::Display for ForFormatting<'_, TrtDefId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let trt_def_id = self.t;

        match self.global_storage.trt_def_store.get(trt_def_id).name {
            Some(name) if !self.opts.expand => {
                write!(f, "{name}")
            }
            _ => {
                write!(f, "trait {{..}}")
            }
        }
    }
}
