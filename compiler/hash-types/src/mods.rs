//! Contains structures to keep track of modules and information relating to
//! them.
use std::fmt;

use hash_source::{identifier::Identifier, SourceId};
use hash_utils::{
    new_sequence_store_key, new_store, new_store_key,
    store::{CloneStore, DefaultSequenceStore},
};

use crate::{
    defs::{DefArgsId, DefMember, DefParamsId},
    fmt::{ForFormatting, PrepareForFormatting},
    scope::ScopeId,
    symbols::Symbol,
    terms::TermId,
    trts::TrtDefId,
};

// -- OLD --

/// The origin of a module: was it defined in a `mod` block, an anonymous `impl`
/// block, or an `impl Trait` block?
#[derive(Debug, Clone, Copy, Hash)]
pub enum ModDefOriginOld {
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
pub struct ModDefOld {
    pub name: Option<Identifier>,
    pub origin: ModDefOriginOld,
    pub members: ScopeId,
}

new_store_key!(pub ModDefIdOld);
new_store!(pub ModDefStoreOld<ModDefIdOld, ModDefOld>);

impl PrepareForFormatting for ModDefIdOld {}

impl fmt::Display for ForFormatting<'_, ModDefIdOld> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mod_def_id = self.t;
        let mod_def = self.global_storage.mod_def_store.get(mod_def_id);

        match mod_def.name {
            Some(name) if !self.opts.expand => {
                write!(f, "{name}")
            }
            _ => match mod_def.origin {
                ModDefOriginOld::TrtImpl(trt_def_id) => {
                    write!(f, "impl {} {{..}}", trt_def_id.for_formatting(self.global_storage))
                }
                ModDefOriginOld::AnonImpl => {
                    write!(f, "impl {{..}}")
                }
                ModDefOriginOld::Mod => {
                    write!(f, "mod {{..}}")
                }
                ModDefOriginOld::Source(_) => {
                    // @@TODO: show the source path
                    write!(f, "source(..)")
                }
            },
        }
    }
}

// -- NEW --

/// Information about a trait being implemented.
///
/// Arguments in `args` could be referencing variables bound by the definition's
/// params.
#[derive(Debug, Clone, Copy)]
pub struct TrtImplData {
    pub trt: TrtDefId,
    pub args: DefArgsId,
}

/// The kind of a module.
#[derive(Debug, Clone, Copy)]
pub enum ModKind {
    /// Defined as a trait implementation.
    ///
    /// Might reference parameters in the mod def.
    TrtImpl(TrtImplData),
    /// Defined as a module (`mod` block).
    ModBlock,
    /// Defined as a file module or interactive.
    Source(SourceId),
}

new_sequence_store_key!(pub ModMembersId);
pub type ModMembersStore = DefaultSequenceStore<ModMembersId, DefMember<ModDefId>>;
pub type ModMemberId = (ModMembersId, usize);

/// A module definition.
///
/// This contains a name, parameters, a kind, and a set of members.
#[derive(Debug, Clone, Copy)]
pub struct ModDef {
    pub name: Symbol,
    pub params: DefParamsId,
    pub kind: ModKind,
    pub members: ModMembersId,

    /// The name of the "Self" type in the scope of the trait definition.
    pub self_type_name: Symbol,
}

new_store_key!(pub ModDefId);
new_store!(pub ModDefStore<ModDefId, ModDef>);
