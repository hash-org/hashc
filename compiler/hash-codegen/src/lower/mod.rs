//! This module is responsible for converting Hash IR into the target code
//! backend via the code generation traits. This minimizes the amount of code
//! that needs to be shared between the different backends, so they can all
//! deal with the specifics of each backend within the particular crate.

use std::iter;

use fixedbitset::FixedBitSet;
use hash_abi::FnAbiId;
use hash_ir::{
    ir::{self, Local},
    traversal,
    ty::InstanceId,
};
use hash_utils::{index_vec::IndexVec, store::Store};

use self::{abi::FnAbiError, locals::LocalRef, operands::OperandRef, place::PlaceRef};
use crate::traits::{
    builder::BlockBuilderMethods, layout::LayoutMethods, misc::MiscBuilderMethods, HasCtxMethods,
};

pub mod abi;
pub mod block;
pub mod debug_info;
pub mod intrinsics;
pub mod locals;
pub mod operands;
pub mod place;
pub mod rvalue;
pub mod statement;
pub mod terminator;
pub mod utils;

/// This enum is used to track the status of a basic block during the
/// lowering process. This is used to avoid creating multiple basic blocks IDs
/// for the same Hash IR block.
pub enum BlockStatus<BasicBlock> {
    /// The block has not been lowered yet.
    UnLowered,

    /// Nothing has been lowered for this block, and nothing will
    /// be lowered. This occurs when two blocks have been merged
    /// into a single backend basic block.
    Skip,

    /// The block has been lowered, and the basic block ID is stored here.
    Lowered(BasicBlock),
}

/// This struct contains all the information required to convert Hash IR into
/// the target code backend.
pub struct FnBuilder<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> {
    /// The body that is being converted into the target backend.
    body: &'b ir::Body,

    /// The code generation context.
    ctx: &'a Builder::CodegenCtx,

    /// The function that is being built.
    function: Builder::Function,

    /// The [FnAbi] of the function that is being lowered.
    fn_abi: FnAbiId,

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

    /// A map that denotes the "lowering" status of each block from an
    /// [ir::BasicBlock] to a [`Builder::BasicBlock`]. This is used to
    /// to not only keep track of which blocks have been lowered, but to
    /// also facilitate the ability to merge blocks together during the
    /// lowering process.
    block_map: IndexVec<ir::BasicBlock, BlockStatus<Builder::BasicBlock>>,
}

impl<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> FnBuilder<'a, 'b, Builder> {
    /// Create a new [FnBuilder] instance.
    pub fn new(
        fn_abi: FnAbiId,
        body: &'b ir::Body,
        ctx: &'a Builder::CodegenCtx,
        func: Builder::Function,
        starting_block: Builder::BasicBlock,
    ) -> Self {
        // Verify that the IR body has resolved all "constant" references
        // as they should be resolved by this point.
        //
        // @@Todo: where do `#run` directives fit into this scheme?
        assert!(body.needed_constants.is_empty());

        let block_map = body
            .blocks()
            .indices()
            .map(|index| {
                if index == ir::START_BLOCK {
                    BlockStatus::Lowered(starting_block)
                } else {
                    BlockStatus::UnLowered
                }
            })
            .collect();

        Self {
            body,
            ctx,
            fn_abi,
            function: func,
            block_map,
            locals: IndexVec::with_capacity(body.declarations.len()),
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
pub fn codegen_ir_body<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>>(
    instance: InstanceId,
    body: &'b ir::Body,
    ctx: &'a Builder::CodegenCtx,
) -> Result<(), FnAbiError> {
    // @@Todo: compute debug info about each local

    let func = ctx.get_fn(instance);

    let abis = ctx.cg_ctx().abis();

    let fn_abi = abis.create_fn_abi(ctx, instance);
    let is_return_indirect = abis.map_fast(fn_abi, |abi| abi.ret_abi.is_indirect());

    // create the starting block, this is needed since we always specify
    // that the initial block is in "use".
    let starting_block = Builder::append_block(ctx, func, "start");

    // create a new function builder and a builder for the starting block
    let mut fn_builder = FnBuilder::new(fn_abi, body, ctx, func, starting_block);
    let mut builder = Builder::build(fn_builder.ctx, starting_block);

    // Allocate space for all the locals.
    let memory_locals = locals::compute_non_ssa_locals(&fn_builder);

    fn_builder.locals = {
        let args = allocate_argument_locals(&fn_builder, &mut builder, &memory_locals);

        let mut allocate = |local: Local| {
            // we need to get the type and layout from the local
            let decl = &fn_builder.body.declarations[local];
            let info = fn_builder.ctx.layout_of(decl.ty);

            if local == ir::RETURN_PLACE && is_return_indirect {
                let value = builder.get_param(0);
                return LocalRef::Place(PlaceRef::new(&builder, value, info));
            }

            // If this is a memory local, then we need to use a place, otherwise
            // just use an operand
            if memory_locals.contains(local.index()) {
                LocalRef::Place(PlaceRef::new_stack(&mut builder, info))
            } else {
                LocalRef::new_operand(&builder, info)
            }
        };

        // Deal with the return place local first...
        let ret_local = allocate(ir::RETURN_PLACE);

        iter::once(ret_local).chain(args).chain(fn_builder.body.vars_iter().map(allocate)).collect()
    };

    // @@Todo: we need to set some debug information for all of the
    // newly allocated locals that we have just generated as arguments.

    // Finally, we can generate the body of the function by
    // traversing the control flow graph in reverse post-order
    // as the natural control-flow order of the function.
    for (block, _) in traversal::ReversePostOrder::new_from_start(fn_builder.body) {
        fn_builder.codegen_block(block);
    }

    Ok(())
}

/// Function that deals with allocating argument locals. This is
/// in it's own function due to the process being more complicated
/// when dealing with ABI specifications, and possibly (in the future)
/// variadic arguments that are passed to the function.
fn allocate_argument_locals<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>>(
    fn_ctx: &FnBuilder<'a, 'b, Builder>,
    builder: &mut Builder,
    memory_locals: &FixedBitSet,
) -> Vec<LocalRef<Builder::Value>> {
    let body = fn_ctx.body;

    // If the return_ty is `indirect`, then this should be set to one?
    let mut param_index = 0;

    body.args_iter()
        .enumerate()
        .map(|(arg_index, local)| {
            let arg_abi = builder.cg_ctx().abis().get_arg_abi(fn_ctx.fn_abi, arg_index);

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

                        return local(OperandRef::from_immediate_value_or_scalar_pair(
                            builder,
                            arg_value,
                            arg_abi.info,
                        ));
                    }

                    // All other pass modes imply that there must be an allocation
                    // made to pass this argument
                    _ => {}
                }
            }

            // Otherwise, just allocate it on the stack
            let tmp = PlaceRef::new_stack(builder, arg_abi.info);
            builder.store_fn_arg(&arg_abi, &mut param_index, tmp);
            LocalRef::Place(tmp)
        })
        .collect()
}
