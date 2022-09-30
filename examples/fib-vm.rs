use std::borrow::Cow;

use budlang::vm::{Bud, Comparison, Function, Instruction, Value};

fn main() {
    const ARG_N: usize = 0;
    let fib = Function {
        arg_count: 1,
        variable_count: 0,
        code: vec![
            // if v0 <= 2
            Instruction::Push(Value::Integer(2)),
            Instruction::PushArg(ARG_N),
            Instruction::Compare(Comparison::LessThanOrEqual),
            Instruction::If { false_jump_to: 6 },
            Instruction::Push(Value::Integer(1)),
            Instruction::Return,
            // self(n - 1) (result left on stack)
            Instruction::Push(Value::Integer(1)),
            Instruction::PushArg(ARG_N),
            Instruction::Sub,
            Instruction::Call {
                vtable_index: None,
                arg_count: 1,
            },
            // self(n - 2) (result left on stack)
            Instruction::Push(Value::Integer(2)),
            Instruction::PushArg(ARG_N),
            Instruction::Sub,
            Instruction::Call {
                vtable_index: None,
                arg_count: 1,
            },
            // add the two values together
            Instruction::Add,
        ],
    };
    let mut context = Bud::empty().with_function("fibonacci", fib);
    let result: i64 = context
        .run(Cow::Borrowed(&[
            Instruction::Push(Value::Integer(35)),
            Instruction::Call {
                vtable_index: Some(0),
                arg_count: 1,
            },
        ]))
        .unwrap();
    // assert_eq!(context.stack.len(), 1);
    assert_eq!(result, 9227465);
}

#[test]
fn runs() {
    main()
}
