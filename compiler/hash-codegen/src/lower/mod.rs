//! This module is responsible for converting Hash IR into the target code
//! backend via the code generation traits. This minimizes the amount of code
//! that needs to be shared between the different backends, so they can all
//! deal with the specifics of each backend within the particular crate.

use hash_abi::FnAbi;
use hash_ir::ir;

use crate::traits::CodeGen;

pub(crate) mod locals;
pub(crate) mod operands;
pub(crate) mod place;
pub(crate) mod rvalue;

/// This struct contains all the information required to convert Hash IR into
/// the target code backend.
pub struct FnBuilder<'b, 'ir, Builder: CodeGen<'b>> {
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

impl<'b, 'ir, Builder: CodeGen<'b>> FnBuilder<'b, 'ir, Builder> {
    /// Create a new [FnBuilder] instance.
    pub fn new(
        body: &'ir ir::Body,
        ctx: &'b Builder::CodegenCtx,
        function: Builder::Function,
        fn_abi: &'ir FnAbi,
    ) -> Self {
        // Verify that the IR body has resolved all "constant" references
        // as they should be resolved by this point.
        //
        // @@Todo: where do `#run` directives fit into this scheme?
        assert!(body.needed_constants.is_empty());

        Self { body, ctx, function, fn_abi, unreachable_block: None }
    }

    /// This is the main entry point for converting the IR body into the
    /// target backend. The process is as follows:
    ///
    /// 1. Analyse what locals are declared and what kind of locals they
    /// are. This is done so that we can avoid allocating space on the stack
    /// for locals that are possibly immediate values or just temporaries.
    ///
    /// 2. Generate debug information for the function, and any of the locals
    /// that are used within the function.
    ///
    /// 3. Traverse the control flow graph in post-order and generate each
    /// block in the function.
    pub fn build(&mut self) {}
}
