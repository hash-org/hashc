//! Contains structures to keep track of nominal type definitions and
//! information relating to them.
use std::{collections::HashMap, fmt};

use hash_source::identifier::Identifier;
use hash_utils::{new_store, new_store_key, store::CloneStore};

use crate::{
    fmt::{ForFormatting, PrepareForFormatting},
    params::ParamsId,
};

/// The fields of a struct.
#[derive(Debug, Clone, Copy)]
pub enum StructFields {
    /// An explicit set of fields, as a set of parameters.
    Explicit(ParamsId),
    /// The struct does not have any accessible parameters.
    ///
    /// This is used for core language definitions that will be filled in later
    /// in the compiler pipeline.
    Opaque,
}

/// A struct definition, containing a binding name and a set of fields.
#[derive(Debug, Clone, Copy)]
pub struct StructDef {
    pub name: Option<Identifier>,
    pub fields: StructFields,
}

/// An enum variant, containing a variant name and a set of fields.
///
/// Structurally the same as a struct.
#[derive(Debug, Clone, Copy)]
pub struct EnumVariant {
    pub name: Identifier,
    pub fields: Option<ParamsId>,
}

/// An enum definition, containing a binding name and a set of variants.
#[derive(Debug, Clone)]
pub struct EnumDef {
    /// The name of the `EnumDef`, useful for error reporting
    pub name: Option<Identifier>,
    /// All of the defined variants that occur within the [EnumDef].
    pub variants: HashMap<Identifier, EnumVariant>,
}

/// An enum variant value, consisting of a [NominalDefId] pointing to an enum,
/// as well as the variant of the enum in the form of an [Identifier].
///
/// Has a level 0 type.
#[derive(Debug, Clone, Copy)]
pub struct EnumVariantValue {
    pub enum_def_id: NominalDefId,
    pub variant_name: Identifier,
}

/// A unit definition.
///
/// This is a nominal type with a single constant constructor.
#[derive(Debug, Clone, Copy)]
pub struct UnitDef {
    pub name: Option<Identifier>,
}

/// A nominal definition, which for now is either a struct, an enum, or a unit.
#[derive(Debug, Clone)]
pub enum NominalDef {
    /// A struct definition.
    Struct(StructDef),
    /// @@Todo: delete
    Enum(EnumDef),
    /// A unit definition.
    Unit(UnitDef),
}

impl NominalDef {
    /// Get the name of the [NominalDef], if any.
    pub fn name(&self) -> Option<Identifier> {
        match self {
            NominalDef::Struct(def) => def.name,
            NominalDef::Enum(def) => def.name,
            NominalDef::Unit(def) => def.name,
        }
    }
}

new_store_key!(pub NominalDefId);
new_store!(pub NominalDefStore<NominalDefId, NominalDef>);

impl PrepareForFormatting for NominalDefId {}

impl fmt::Display for ForFormatting<'_, NominalDefId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.global_storage.nominal_def_store.get(self.t) {
            NominalDef::Struct(StructDef { name: Some(name), .. })
            | NominalDef::Enum(EnumDef { name: Some(name), .. })
            | NominalDef::Unit(UnitDef { name: Some(name) })
                if !self.opts.expand =>
            {
                write!(f, "{name}")
            }
            // @@Future: we can actually print out the location of these definitions, which might
            // help with debugging.
            // Perhaps also we can have a flag to print out all the members.
            NominalDef::Struct(_) => {
                write!(f, "struct(..)")
            }
            NominalDef::Enum(_) => {
                write!(f, "enum(..)")
            }
            NominalDef::Unit(_) => {
                write!(f, "unit()")
            }
        }
    }
}
