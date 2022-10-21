use std::borrow::Cow;

use budlang::{
    symbol::Symbol,
    vm::{
        Bud, CompareAction, Comparison, Destination, Function, Instruction, Value, ValueOrSource,
    },
};

fn main() {
    const ARG_N: usize = 0;
    let fib = Function {
        name: Symbol::from("fibonacci"),
        arg_count: 1,
        variable_count: 2,
        code: vec![
            // if v0 <= 2
            Instruction::Compare {
                comparison: Comparison::LessThanOrEqual,
                left: ValueOrSource::Argument(ARG_N),
                right: ValueOrSource::Value(Value::Integer(2)),
                action: CompareAction::JumpIfFalse(2),
            },
            Instruction::Return(Some(ValueOrSource::Value(Value::Integer(1)))),
            // self(n - 1) (result left on stack)
            Instruction::Sub {
                left: ValueOrSource::Argument(ARG_N),
                right: ValueOrSource::Value(Value::Integer(1)),
                destination: Destination::Stack,
            },
            Instruction::Call {
                vtable_index: None,
                arg_count: 1,
                destination: Destination::Variable(0),
            },
            // self(n - 2) (result left on stack)
            Instruction::Sub {
                left: ValueOrSource::Argument(ARG_N),
                right: ValueOrSource::Value(Value::Integer(2)),
                destination: Destination::Stack,
            },
            Instruction::Call {
                vtable_index: None,
                arg_count: 1,
                destination: Destination::Variable(1),
            },
            // add the two values together
            Instruction::Add {
                left: ValueOrSource::Variable(0),
                right: ValueOrSource::Variable(1),
                destination: Destination::Return,
            },
        ],
    };
    let mut context = Bud::empty().with_function(fib);
    let result: i64 = context
        .run(
            Cow::Borrowed(&[
                Instruction::Push(ValueOrSource::Value(Value::Integer(35))),
                Instruction::Call {
                    vtable_index: Some(0),
                    arg_count: 1,
                    destination: Destination::Stack,
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