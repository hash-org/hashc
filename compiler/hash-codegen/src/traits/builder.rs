//! This module defines the core trait of the code generation backend
//! which is used to generate code for a particular backend. This trait
//! provides IR builder methods that the compiler uses to generate code
//! from Hash IR.

use super::{
    debug::BuildDebugInfoMethods, intrinsics::BuildIntrinsicCallMethods, target::HasTargetSpec,
    HasCodegen,
};

/// This trait defines all methods required to convert a Hash IR [BasicBlock]
/// into the backend equivalent.
pub trait BlockBuilderMethods<'b>:
    HasCodegen<'b> + BuildIntrinsicCallMethods<'b> + BuildDebugInfoMethods + HasTargetSpec
{
    // @@Todo: write the code generation methods
}
