//! Hash Compiler VM tests.
use hash_vm::{builder::BytecodeBuilder, bytecode::register::Register, inst, r, vm::Interpreter};

#[test]
fn push_two_and_add() {
    let mut builder = BytecodeBuilder::default();

    let r0 = r!(0);
    builder.append(inst! {
        write16 [0], #[2];
        write16 [1], #[2];
        add16 [0], [1];
    });

    let mut vm = Interpreter::new();

    // @@Todo: this is definitely not correct, as we'd
    // still need to ensure that we've got all of the right
    // labels and offsets set up within the bytecode, i.e.
    // function addresses, block label addresses.
    vm.set_program(builder.instructions);
    vm.run().unwrap();
    assert_eq!(vm.registers().get_register16(r0), 4);
}
