//! Contains structures to keep track of modules and information relating to
//! them.
use std::fmt;

use hash_source::{identifier::Identifier, SourceId};
use hash_utils::{new_store, new_store_key, store::CloneStore};

use crate::old::{
    fmt::{ForFormatting, PrepareForFormatting},
    scope::ScopeId,
    terms::TermId,
};

/// The origin of a module: was it defined in a `mod` block, an anonymous `impl`
/// block, or an `impl Trait` block?
#[derive(Debug, Clone, Copy, Hash)]
pub enum ModDefOrigin {
    /// Defined as a trait implementation (for the given term that should
    /// resolve to a trait value).
    TrtImpl(TermId),
    /// Defined as an anonymous implementation.
    AnonImpl,
    /// Defined as a module (`mod` block).
    Mod,
    /// Defined as a file module or interactive.
    Source(SourceId),
}

/// A module definition, which is of a given origin, has a binding name, and
/// contains some constant members.
#[derive(Debug, Clone)]
pub struct ModDef {
    pub name: Option<Identifier>,
    pub origin: ModDefOrigin,
    pub members: ScopeId,
}

new_store_key!(pub ModDefId);
new_store!(pub ModDefStore<ModDefId, ModDef>);

impl PrepareForFormatting for ModDefId {}

impl fmt::Display for ForFormatting<'_, ModDefId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mod_def_id = self.t;
        let mod_def = self.global_storage.mod_def_store.get(mod_def_id);

        match mod_def.name {
            Some(name) if !self.opts.expand => {
                write!(f, "{name}")
            }
            _ => match mod_def.origin {
                ModDefOrigin::TrtImpl(trt_def_id) => {
                    write!(f, "impl {} {{..}}", trt_def_id.for_formatting(self.global_storage))
                }
                ModDefOrigin::AnonImpl => {
                    write!(f, "impl {{..}}")
                }
                ModDefOrigin::Mod => {
                    write!(f, "mod {{..}}")
                }
                ModDefOrigin::Source(_) => {
                    // @@TODO: show the source path
                    write!(f, "source(..)")
                }
            },
        }
    }
}
