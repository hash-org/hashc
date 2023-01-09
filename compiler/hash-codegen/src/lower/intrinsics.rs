//! Module that hosts all of the logic that deals with emitting
//! code and resolving references to intrinsic function calls.

use hash_abi::FnAbi;

use super::FnBuilder;
use crate::traits::builder::BlockBuilderMethods;

/// Defines all of the intrinsics that are present within the
/// language runtime, and can be accessed by the language.
///
/// @@Todo: this needs to record the number of arguments the intrinsic
/// takes, and possibly other information.
pub enum Intrinsic {
    Panic,
}

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {
    /// Resolve a reference to an [Intrinsic].
    pub(super) fn resolve_intrinsic(
        &self,
        _builder: &mut Builder,
        _intrinsic: Intrinsic,
    ) -> (FnAbi, Builder::Value) {
        todo!()
    }
}
