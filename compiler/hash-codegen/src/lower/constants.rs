//! Contains logic for lowering Hash IR constants into
//! backend specific constant representations.

use super::FnBuilder;
use crate::traits::builder::BlockBuilderMethods;

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {}
