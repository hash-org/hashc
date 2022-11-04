//! General definition-related utilities

use hash_utils::{new_sequence_store_key, store::DefaultSequenceStore};
use utility_types::omit;

use super::{args::PatArgsId, pats::Spread};
use crate::new::{args::ArgsId, params::ParamsId, symbols::Symbol, terms::TermId, tys::TyId};

/// A group of definition parameters
///
/// This is either a set of implicit parameters `<a_1: A_1,...,a_n: A_N>` or a
/// set of explicit parameters `(a_1: A_1,...,a_n: A_N)`.
#[omit(DefParamGroupData, [id], [Debug, Clone, Copy])]
#[derive(Debug, Clone, Copy)]
pub struct DefParamGroup {
    pub id: DefParamGroupId,
    pub implicit: bool,
    pub params: ParamsId,
}
new_sequence_store_key!(pub DefParamsId);
pub type DefParamsStore = DefaultSequenceStore<DefParamsId, DefParamGroup>;
pub type DefParamGroupId = (DefParamsId, usize);

/// A group of definition arguments
///
/// This contains the original parameter group of the definition, as well as
/// set of arguments for it, ordered by the original parameters.
#[omit(DefArgGroupData, [id], [Debug, Clone, Copy])]
#[derive(Debug, Clone, Copy)]
pub struct DefArgGroup {
    pub id: DefArgGroupId,
    pub param_group: DefParamGroupId,
    pub args: ArgsId,
}
new_sequence_store_key!(pub DefArgsId);
pub type DefArgsStore = DefaultSequenceStore<DefArgsId, DefArgGroup>;
pub type DefArgGroupId = (DefArgsId, usize);

/// A group of definition pattern arguments
///
/// This contains the original parameter group of the definition, as well as
/// set of pattern arguments for it, ordered by the original parameters.
#[omit(DefPatArgGroupData, [id], [Debug, Clone, Copy])]
#[derive(Debug, Clone, Copy)]
pub struct DefPatArgGroup {
    pub id: DefPatArgGroupId,
    pub param_group: DefParamGroupId,
    pub pat_args: PatArgsId,
    /// The spread in this group of patterns, if any.
    pub spread: Option<Spread>,
}
new_sequence_store_key!(pub DefPatArgsId);
pub type DefPatArgsStore = DefaultSequenceStore<DefPatArgsId, DefPatArgGroup>;
pub type DefPatArgGroupId = (DefPatArgsId, usize);

/// A member of a definition.
///
/// A definition might be a trait, impl block, or a module.
///
/// Includes a name, the original definition ID, an index into the original
/// definition's members, as well as the type of the member, and an optional
/// value of the member.
#[derive(Debug, Clone, Copy)]
pub struct DefMember<OriginalDefMembersId> {
    pub id: (OriginalDefMembersId, usize),
    pub name: Symbol,
    pub ty: TyId,
    pub value: Option<TermId>,
}

/// The data version of [`DefMember`] (i.e. without ID).
#[derive(Debug, Clone, Copy)]
pub struct DefMemberData {
    pub name: Symbol,
    pub ty: TyId,
    pub value: Option<TermId>,
}
