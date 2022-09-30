use std::borrow::Cow;

use budlang::vm::{Comparison, Context, Function, Operation, Value};

fn main() {
    const ARG_N: usize = 0;
    let fib = Function {
        arg_count: 1,
        variable_count: 0,
        ops: vec![
            // if v0 <= 2
            Operation::Push(Value::Integer(2)),
            Operation::PushArg(ARG_N),
            Operation::Compare(Comparison::LessThanOrEqual),
            Operation::If { false_jump_to: 6 },
            Operation::Push(Value::Integer(1)),
            Operation::Return,
            // self(n - 1) (result left on stack)
            Operation::Push(Value::Integer(1)),
            Operation::PushArg(ARG_N),
            Operation::Sub,
            Operation::Call {
                vtable_index: None,
                arg_count: 1,
            },
            // self(n - 2) (result left on stack)
            Operation::Push(Value::Integer(2)),
            Operation::PushArg(ARG_N),
            Operation::Sub,
            Operation::Call {
                vtable_index: None,
                arg_count: 1,
            },
            // add the two values together
            Operation::Add,
        ],
    };
    let mut context = Context::empty().with_function("fibonacci", fib);
    let result: i64 = context
        .run(Cow::Borrowed(&[
            Operation::Push(Value::Integer(35)),
            Operation::Call {
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
