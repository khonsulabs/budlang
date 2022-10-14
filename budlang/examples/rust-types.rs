use std::io::{stdout, Write};

use budlang::{
    symbol::Symbol,
    vm::{Bud, DynamicValue, FaultKind, PoppedValues, Value, ValueKind},
};

fn main() {
    // Create a runtime with a function `stdout()` which returns our dynamic
    // `StdOut` type.
    let mut bud = Bud::empty().with_native_function("stdout", |args: &mut PoppedValues<'_>| {
        args.verify_empty()?;
        Ok(Value::dynamic(StdOut))
    });

    // Write to stdout by calling `write` on `StdOut`.
    let result: String = bud
        .run_source(r#"stdout().write("Hello, World!")"#)
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

    fn kind(&self) -> &'static str {
        "StdOut"
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
