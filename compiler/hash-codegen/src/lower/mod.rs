//! This module is responsible for converting Hash IR into the target code
//! backend via the code generation traits. This minimizes the amount of code
//! that needs to be shared between the different backends, so they can all
//! deal with the specifics of each backend within the particular crate.

use hash_abi::FnAbi;
use hash_ir::ir;

use crate::traits::{builder::BlockBuilderMethods, CodeGen};

pub(crate) mod operands;
pub(crate) mod place;

/// This struct contains all the information required to convert Hash IR into
/// the target code backend.
pub struct FnBuilder<'b, 'ir, Builder: CodeGen<'ir>> {
    /// The body that is being converted into the target backend.
    body: &'ir ir::Body,

    /// The code generation context.
    ctx: &'b Builder::CodegenCtx,

    /// The function that is being built.
    function: Builder::Function,

    /// The function ABI detailing all the information about
    /// arguments, return types, layout and calling conventions.
    fn_abi: &'ir FnAbi,

    /// A commonly shared "unreachable" block in order to avoid
    /// having multiple basic blocks that are "unreachable".
    unreachable_block: Option<Builder::BasicBlock>,
}

impl<'b, 'ir, Builder: CodeGen<'ir>> FnBuilder<'b, 'ir, Builder> {
    /// Create a new [FnBuilder] instance.
    pub fn new(
        body: &'ir ir::Body,
        ctx: &'b Builder::CodegenCtx,
        function: Builder::Function,
        fn_abi: &'ir FnAbi,
    ) -> Self {
        // Verify that the IR body has resolved all "constant" references
        // as they should be resolved by this point.
        assert!(body.needed_constants.is_empty());

        Self { body, ctx, function, fn_abi, unreachable_block: None }
    }
}
