//! This module hosts all of the logic for converting IR
//! [Terminator]s into corresponding target backend IR.
//! Given that the Hash IR does not necessarily have a
//! one-to-one mapping with the target IR, some terminators
//! might not exist in the target IR. For example, the
//! [TerminatorKind::Call] terminator might not exist in
//! some target IRs. In this case, the [TerminatorKind::Call],
//! is lowered as two [BasicBlock]s being "merged" together
//! into a single [BasicBlock]. The builder API will denote
//! whether two blocks have been merged together.

use super::FnBuilder;
use crate::traits::builder::BlockBuilderMethods;

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {}
