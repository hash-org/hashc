//! Hash Compiler VM bytecode building module.
//!
//! This module holds utilities and data structures to generate bytecode and
//! store it in the format that the VM expects.

mod func;
mod instruction;
mod resolution;

use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
};

use hash_abi::FnAbiId;
use hash_repr::ty::InstanceId;

pub use self::func::FunctionBuilder;
use crate::bytecode::Instruction;

#[derive(Debug)]
pub struct FunctionCtx {
    /// The ABI of the function, this is used to generate
    /// the correct instructions for the function, to read the
    /// arguments and return values correctly.
    pub abi: FnAbiId,

    /// The address of the function within the entire bytecode program.
    pub offset: usize,
}

#[derive(Debug)]
pub struct BytecodeBuilder {
    /// The entire bytecode program, this contains all of the
    /// functions and their instructions.
    pub instructions: Vec<Instruction>,

    /// Current function that is being built.
    ///
    /// N.B. We would need to store this somewhere differently if we wanted to
    /// make this thread-safe.
    current_function: Cell<Option<InstanceId>>,

    /// The function context store, this is used to store the function contexts.
    function_ctxs: RefCell<HashMap<InstanceId, FunctionBuilder>>,
}

impl BytecodeBuilder {
    /// Create a new [BytecodeBuilder].
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            function_ctxs: RefCell::new(HashMap::new()),
            current_function: Cell::new(None),
        }
    }

    /// Add a new function to the bytecode builder.
    ///
    /// This will also configure the builder to use the newly added function
    /// as the current function.
    pub fn new_function(&self, fn_builder: FunctionBuilder) {
        let FunctionBuilder { instance, .. } = fn_builder;
        self.current_function.set(Some(instance));
        self.function_ctxs.borrow_mut().insert(instance, fn_builder);
    }

    /// Add a single instruction to the bytecode builder.
    pub fn add_instruction(&mut self, instruction: Instruction) {
        self.instructions.push(instruction);
    }

    /// Append a block of instructions to the bytecode builder.
    ///
    /// This method accepts a `Vec<Instruction>` which can be conveniently
    /// created using the `inst!` macro.
    ///
    /// # Example
    ///
    /// ```
    /// use hash_vm::{builder::BytecodeBuilder, inst};
    ///
    /// let mut builder = BytecodeBuilder::new();
    /// builder.append(inst! {
    ///     write64 [0], # [42];
    ///     add64 [0], [1];
    /// });
    /// ```
    pub fn append(&mut self, instructions: Vec<Instruction>) {
        self.instructions.extend(instructions);
    }

    /// Get a function builder by its ABI.
    pub fn with_fn_builder<F>(&self, instance: InstanceId, f: F)
    where
        F: FnOnce(&FunctionBuilder),
    {
        let ctx = self.function_ctxs.borrow();
        let fn_builder = ctx.get(&instance).unwrap();
        f(fn_builder)
    }

    pub fn with_fn_builder_mut<F, T>(&self, instance: InstanceId, f: F) -> T
    where
        F: FnOnce(&mut FunctionBuilder) -> T,
    {
        let mut function_ctxs = self.function_ctxs.borrow_mut();
        let fn_builder = function_ctxs.get_mut(&instance).unwrap();
        f(fn_builder)
    }

    /// Call a closure with the current function builder.
    ///
    /// This is useful for modifying the current function builder
    /// without having to pass around the instance ID.
    ///
    /// ##Note: This assumes that there is a current function set.
    pub fn with_current_mut<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&mut FunctionBuilder) -> T,
    {
        let instance = self.current_function.get().expect("there must be a current function");
        let mut function_ctxs = self.function_ctxs.borrow_mut();
        let fn_builder = function_ctxs.get_mut(&instance).unwrap();
        f(fn_builder)
    }
}
