use budvm::{
    ir::{
        CodeBlockBuilder, CompareAction, Destination, Instruction, Literal, LiteralOrSource, Scope,
    },
    Comparison, Function, Value, ValueOrSource, VirtualMachine,
};

fn main() {
    let mut block = CodeBlockBuilder::default();
    let arg_n = block.new_argument("n");
    let if_greater_than_two = block.named_label("if_greater_than_two");
    // if n <= 2
    block.push(Instruction::Compare {
        comparison: Comparison::LessThanOrEqual,
        left: LiteralOrSource::from(&arg_n),
        right: LiteralOrSource::from(Literal::Integer(2)),
        action: CompareAction::JumpIfFalse(if_greater_than_two.clone()),
    });
    // return 1
    block.push(Instruction::Return(Some(LiteralOrSource::from(
        Literal::Integer(1),
    ))));
    // else (#if_greater_than_two)
    block.label(if_greater_than_two);
    // n - 1, push result to stack
    block.push(Instruction::Sub {
        left: LiteralOrSource::from(&arg_n),
        right: LiteralOrSource::from(Literal::Integer(1)),
        destination: Destination::Stack,
    });
    // recurse call
    block.push(Instruction::Call {
        function: None,
        arg_count: 1,
        destination: Destination::Stack,
    });
    // n - 2, push result to stack
    block.push(Instruction::Sub {
        left: LiteralOrSource::from(arg_n),
        right: LiteralOrSource::from(Literal::Integer(2)),
        destination: Destination::Stack,
    });
    // recurse call
    block.push(Instruction::Call {
        function: None,
        arg_count: 1,
        destination: Destination::Stack,
    });
    // Add the two variables together, and return the result.
    block.push(Instruction::Add {
        left: LiteralOrSource::Stack,
        right: LiteralOrSource::Stack,
        destination: Destination::Return,
    });
    let block = block.finish();
    println!("IR:");
    println!("{block}");

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
            &[
                budvm::Instruction::Push(ValueOrSource::Value(Value::Integer(10))),
                budvm::Instruction::Call {
                    vtable_index: Some(fibonacci_vtable_index),
                    arg_count: 1,
                    destination: budvm::Destination::Stack,
                },
            ],
            0,
        )
        .unwrap();
    assert_eq!(result, 55);
}

#[test]
fn runs() {
    main()
}
