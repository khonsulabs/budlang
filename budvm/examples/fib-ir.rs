use std::borrow::Cow;

use budvm::{
    ir::{
        CodeBlockBuilder, CompareAction, Destination, Instruction, Literal, LiteralOrSource, Scope,
    },
    Comparison, Function, Value, ValueOrSource, VirtualMachine,
};

fn main() {
    const ARG_N: usize = 0;
    let mut block = CodeBlockBuilder::default();
    let if_greater_than_two = block.new_label();
    // if n <= 2
    block.push(Instruction::Compare {
        comparison: Comparison::LessThanOrEqual,
        left: LiteralOrSource::Argument(ARG_N),
        right: LiteralOrSource::Literal(Literal::Integer(2)),
        action: CompareAction::JumpIfFalse(if_greater_than_two),
    });
    // return 1
    block.push(Instruction::Return(Some(LiteralOrSource::Literal(
        Literal::Integer(1),
    ))));
    // else (#if_greater_than_two)
    block.label(if_greater_than_two);
    // n - 1, push result to stack
    block.push(Instruction::Sub {
        left: LiteralOrSource::Argument(ARG_N),
        right: LiteralOrSource::Literal(Literal::Integer(1)),
        destination: Destination::Stack,
    });
    // recurse call, store result in a variable.
    let n_minus_one = block.new_temporary_variable();
    block.push(Instruction::Call {
        function: None,
        arg_count: 1,
        destination: Destination::Variable(n_minus_one),
    });
    // n - 2, push result to stack
    block.push(Instruction::Sub {
        left: LiteralOrSource::Argument(ARG_N),
        right: LiteralOrSource::Literal(Literal::Integer(2)),
        destination: Destination::Stack,
    });
    // recurse call, store result in a variable.
    let n_minus_two = block.new_temporary_variable();
    block.push(Instruction::Call {
        function: None,
        arg_count: 1,
        destination: Destination::Variable(n_minus_two),
    });
    // Add the two variables together, and return the result.
    block.push(Instruction::Add {
        left: LiteralOrSource::Variable(n_minus_one),
        right: LiteralOrSource::Variable(n_minus_two),
        destination: Destination::Return,
    });
    let block = block.finish();

    // The code block needs to be linked, which will convert the intermediate
    // representation into virtual machine instructions.
    let mut vm = VirtualMachine::empty();
    let block = block.link(&vm).unwrap();
    // Define a new function in the virtual machine using the block we just linked.
    let fibonacci_vtable_index = vm
        .define_function(Function::new("fibonacci", 1, block))
        .unwrap();

    // Invoke the function by pushing a value and then calling the vtable index
    // we received from defining the function.
    let result: i64 = vm
        .run(
            Cow::Borrowed(&[
                budvm::Instruction::Push(ValueOrSource::Value(Value::Integer(35))),
                budvm::Instruction::Call {
                    vtable_index: Some(fibonacci_vtable_index),
                    arg_count: 1,
                    destination: budvm::Destination::Stack,
                },
            ]),
            0,
        )
        .unwrap();
    assert_eq!(result, 9227465);
}

#[test]
fn runs() {
    main()
}
