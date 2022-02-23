use hash_vm::{
    bytecode::Instruction, bytecode_builder::BytecodeBuilder, register::Register, vm::Interpreter,
    vm::InterpreterOptions,
};

#[test]
fn push_two_and_add() {
    let mut builder = BytecodeBuilder::default();

    let l1 = Register::new(0);
    let l2 = Register::new(1);

    builder.add_instruction(Instruction::Add16 { l1, l2 });

    let mut vm = Interpreter::new(InterpreterOptions::default());
    vm.set_program(builder.into());

    // set registers l1 and l2 to appropriate values...
    vm.registers_mut().set_register16(l1, 2);
    vm.registers_mut().set_register16(l2, 2);

    vm.run().unwrap();
    assert_eq!(vm.registers().get_register16(l1), 4);
}
