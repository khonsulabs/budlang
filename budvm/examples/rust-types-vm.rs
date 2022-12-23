use std::io::{stdout, Write};

use budvm::{
    ir::{CodeBlock, Destination, Instruction, Literal, LiteralOrSource},
    DynamicValue, FaultKind, PoppedValues, Symbol, Value, ValueKind, VirtualMachine,
};

fn main() {
    // Create a runtime with a function `stdout()` which returns our dynamic
    // `StdOut` type.
    let mut vm =
        VirtualMachine::empty().with_native_function("stdout", |args: &mut PoppedValues<'_>| {
            args.verify_empty()?;
            Ok(Value::dynamic(StdOut))
        });

    let mut block = CodeBlock::build();

    // Call the stdout function we defined above, and store the result (our
    // StdOut instance) in a temporary variable.
    let stdout = block.new_temporary_variable();
    block.push(Instruction::Call {
        function: Some(Symbol::from("stdout")),
        arg_count: 0,
        destination: Destination::from(&stdout),
    });

    // Call write on our StdOut instance, passing in "Hello, World!".
    block.push(Instruction::Push(LiteralOrSource::from(Literal::from(
        "Hello, World!",
    ))));
    block.push(Instruction::CallInstance {
        target: Some(LiteralOrSource::from(&stdout)),
        name: Symbol::from("write"),
        arg_count: 1,
        destination: Destination::Return,
    });
    // Finish building the ir, link the code block, and execute it.
    let result: String = block
        .finish()
        .link(&vm)
        .unwrap()
        .execute_in(&mut vm)
        .unwrap();

    // The function not only outputs to stdout, but it also returns the value.
    assert_eq!(result, "Hello, World!");
}

#[derive(Debug, Clone)]
pub struct StdOut;

impl DynamicValue for StdOut {
    fn is_truthy(&self) -> bool {
        true
    }

    fn kind(&self) -> Symbol {
        Symbol::from("StdOut")
    }

    fn call(&self, name: &Symbol, args: &mut PoppedValues<'_>) -> Result<Value, FaultKind> {
        // Look up the function being called
        match name.as_str() {
            "write" => {
                let value = args.next_argument(&Symbol::from("value"))?;
                args.verify_empty()?;

                let mut stdout = stdout().lock();
                if let Some(value) = value.as_dynamic::<String>() {
                    // Value is a string, print the string as-is
                    stdout.write_all(value.as_bytes())?;
                } else {
                    // Value isn't a string, use Display to convert it.
                    let value = value.to_string();
                    stdout.write_all(value.as_bytes())?;
                }

                stdout.write_all(b"\n")?;
                stdout.flush()?;
                Ok(value)
            }
            _ => Err(FaultKind::UnknownFunction {
                kind: ValueKind::Dynamic(self.kind()),
                name: name.clone(),
            }),
        }
    }
}

#[test]
fn runs() {
    main();
}
