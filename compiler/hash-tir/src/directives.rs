//! Store to keep track of all the directives in the program, and their targets.

use derive_more::From;
use hash_source::identifier::Identifier;
use hash_utils::store::DefaultPartialStore;
use indexmap::IndexSet;

use crate::{
    data::{CtorDefId, DataDefId},
    fns::FnDefId,
    mods::{ModDefId, ModMemberValue},
    params::ParamId,
    pats::PatId,
    terms::TermId,
    tys::TyId,
};

macro_rules! directive_targets {
    ($($name:ident),* $(,)?) => {
        /// All the atoms in the TIR which are valid targets for directives.
        #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, From)]
        pub enum DirectiveTarget {
           $(
               $name($name),
           )*
        }
    };
}
directive_targets! {
    TermId,
    TyId,
    PatId,
    ParamId,
    FnDefId,
    DataDefId,
    ModDefId,
    CtorDefId,
}

impl From<ModMemberValue> for DirectiveTarget {
    fn from(value: ModMemberValue) -> Self {
        match value {
            ModMemberValue::Fn(fn_def) => Self::FnDefId(fn_def),
            ModMemberValue::Data(data_def) => Self::DataDefId(data_def),
            ModMemberValue::Mod(mod_def) => Self::ModDefId(mod_def),
        }
    }
}

/// A set of directives that have been applied to a target.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AppliedDirectives {
    pub directives: IndexSet<Identifier>,
}

pub type AppliedDirectivesStore = DefaultPartialStore<DirectiveTarget, AppliedDirectives>;
