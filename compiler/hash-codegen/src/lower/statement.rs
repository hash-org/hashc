//! Contains logic for lowering Hash IR [Statement]s into
//! the target backend IR.

use super::FnBuilder;
use crate::traits::builder::BlockBuilderMethods;

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {}
