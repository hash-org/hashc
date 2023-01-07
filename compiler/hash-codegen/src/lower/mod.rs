//! This module is responsible for converting Hash IR into the target code
//! backend via the code generation traits. This minimizes the amount of code
//! that needs to be shared between the different backends, so they can all
//! deal with the specifics of each backend within the particular crate.

use fixedbitset::FixedBitSet;
use hash_abi::FnAbi;
use hash_ir::{
    ir::{self, Local},
    traversal,
};
use index_vec::IndexVec;

use self::{locals::LocalRef, operands::OperandRef, place::PlaceRef};
use crate::traits::{builder::BlockBuilderMethods, layout::LayoutMethods};

pub(crate) mod block;
pub(crate) mod debug_info;
pub(crate) mod locals;
pub(crate) mod operands;
pub(crate) mod place;
pub(crate) mod rvalue;
pub(crate) mod statement;
pub(crate) mod terminator;

/// This struct contains all the information required to convert Hash IR into
/// the target code backend.
pub struct FnBuilder<'b, Builder: BlockBuilderMethods<'b>> {
    /// The body that is being converted into the target backend.
    body: &'b ir::Body,

    /// The code generation context.
    ctx: &'b Builder::CodegenCtx,

    /// The function that is being built.
    function: Builder::Function,

    /// The function ABI detailing all the information about
    /// arguments, return types, layout and calling conventions.
    fn_abi: &'b FnAbi,

    /// The location of where each IR argument/temporary/variable and return
    /// value is stored. Usually, this is a [PlaceRef] which represents an
    /// allocation on the stack, but sometimes we can pre-compute whether the
    /// value will need a stack allocation or not, and in that case we use
    /// an [OperandRef] instead. The conditions for using an [OperandRef] are
    /// the following:
    ///
    /// 1. The type of the local must be judged as an "immediate" by the
    /// backend.
    ///
    /// 2. The operand should not be referenced indirectly:
    ///
    ///    - It's address should not be taken by the `&` operator.
    ///
    ///   - It cannot appear in a projection (e.g. `x.field`).
    ///
    /// 3. The operand must be defined by an [ir::RValue] that can generate
    /// immediate values as judged by [`Self::rvalue_creates_operand`].
    locals: IndexVec<Local, LocalRef<Builder::Value>>,

    /// A commonly shared "unreachable" block in order to avoid
    /// having multiple basic blocks that are "unreachable".
    unreachable_block: Option<Builder::BasicBlock>,
}

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {
    /// Create a new [FnBuilder] instance.
    pub fn new(
        body: &'b ir::Body,
        ctx: &'b Builder::CodegenCtx,
        function: Builder::Function,
        fn_abi: &'b FnAbi,
    ) -> Self {
        // Verify that the IR body has resolved all "constant" references
        // as they should be resolved by this point.
        //
        // @@Todo: where do `#run` directives fit into this scheme?
        assert!(body.needed_constants.is_empty());

        Self {
            body,
            ctx,
            function,
            fn_abi,
            locals: IndexVec::with_capacity(body.declarations.len()),
            unreachable_block: None,
        }
    }
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
pub fn codegen_ir_body<'b, Builder: BlockBuilderMethods<'b>>(
    body: &'b ir::Body,
    ctx: &'b Builder::CodegenCtx,
    function: Builder::Function,
    fn_abi: &'b FnAbi,
) {
    // @@Todo: compute debug info about each local

    // create a new function builder
    let mut fn_builder = FnBuilder::new(body, ctx, function, fn_abi);

    let starting_block = Builder::append_block(fn_builder.ctx, function, "start");
    let mut builder = Builder::build(fn_builder.ctx, starting_block);

    // Allocate space for all the locals.
    let memory_locals = locals::compute_non_ssa_locals(&fn_builder);

    {
        allocate_argument_locals(&mut fn_builder, &mut builder, &memory_locals);

        let mut allocate = |local: Local, info| {
            if local == ir::RETURN_PLACE {
                let value = builder.get_param(0);
                return LocalRef::Place(PlaceRef::new(&mut builder, value, info));
            }

            // If this is a memory local, then we need to use a place, otherwise
            // just use an operand
            if memory_locals.contains(local.index()) {
                LocalRef::Place(PlaceRef::new_stack(&mut builder, info))
            } else {
                LocalRef::new_operand(&mut builder, info)
            }
        };

        // Deal with the return place local first...
        let ret_local = allocate(ir::RETURN_PLACE, fn_builder.fn_abi.ret_abi.info);
        fn_builder.locals[ir::RETURN_PLACE] = ret_local;

        // Finally, deal with the rest of the locals
        for local in fn_builder.body.vars_iter() {
            // we need to get the type and layout from the local
            let decl = &fn_builder.body.declarations[local];
            let info = fn_builder.ctx.layout_of_id(decl.ty);

            fn_builder.locals[local] = allocate(local, info);
        }
    }

    // @@Todo: we need to set some debug information for all of the
    // newly allocated locals that we have just generated as arguments.

    // Finally, we can generate the body of the function by
    // traversing the control flow graph in reverse post-order
    // as the natural control-flow order of the function.
    for (block, _) in traversal::ReversePostOrder::new_from_start(fn_builder.body) {
        fn_builder.codegen_block(block);
    }
}

/// Function that deals with allocating argument locals. This is
/// in it's own function due to the process being more complicated
/// when dealing with ABI specifications, and possibly (in the future)
/// variadic arguments that are passed to the function.
fn allocate_argument_locals<'b, Builder: BlockBuilderMethods<'b>>(
    fn_ctx: &mut FnBuilder<'b, Builder>,
    builder: &mut Builder,
    memory_locals: &FixedBitSet,
) -> Vec<LocalRef<Builder::Value>> {
    let body = fn_ctx.body;

    // If the return_ty is `indirect`, then this should be set to one?
    let mut param_index = 0;

    body.args_iter()
        .enumerate()
        .map(|(arg_index, local)| {
            let arg_abi = &fn_ctx.fn_abi.args[arg_index];

            // Check if we can just pass these arguments directly...
            if !memory_locals.contains(local.index()) {
                let local = |op| LocalRef::Operand(Some(op));

                // Based on the pass mode of the argument, we might have
                // to do some extra work to get the argument into the
                // correct form.
                match arg_abi.mode {
                    hash_abi::PassMode::Ignore => {
                        return local(OperandRef::new_zst(builder, arg_abi.info));
                    }
                    hash_abi::PassMode::Direct(_) => {
                        let arg_value = builder.get_param(param_index);
                        param_index += 1;

                        return local(OperandRef::from_immediate(arg_value, arg_abi.info));
                    }

                    // All other pass modes imply that there must be an allocation
                    // made to pass this argument
                    _ => {}
                }
            }

            // Otherwise, just allocate it on the stack
            let tmp = PlaceRef::new_stack(builder, arg_abi.info);
            builder.store_fn_arg(arg_abi, &mut param_index, tmp);
            LocalRef::Place(tmp)
        })
        .collect()
}
