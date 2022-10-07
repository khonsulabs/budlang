use std::{fmt::Display, vec};

use crate::{
    symbol::Symbol,
    vm::{
        self, Bud, DynamicFault, DynamicValue, Fault, FaultKind, FaultOrPause, Instruction,
        PoppedValues, Value, ValueOrSource,
    },
    Error,
};

macro_rules! assert_run {
    ($source:literal, $result:expr) => {
        let mut context = Bud::empty();
        let expected_result = $result;
        let result: Value = context.run_source($source).unwrap();
        if result != $result {
            panic!(
                "{} returned {result:?}, expected {expected_result:?}",
                $source
            );
        }
    };
}

#[test]
fn comparisons() {
    // Equal
    assert_run!("1 = 2", false);
    assert_run!("2 = 2", true);
    // Not Equal
    assert_run!("1 != 2", true);
    assert_run!("2 != 2", false);
    // Less than
    assert_run!("1 < 2", true);
    assert_run!("2 < 1", false);

    // Less than or equal
    assert_run!("1 <= 2", true);
    assert_run!("2 <= 2", true);
    assert_run!("3 <= 2", false);

    // Greater than
    assert_run!("2 > 1", true);
    assert_run!("1 > 2", false);

    // Greater than or equal
    assert_run!("2 >= 1", true);
    assert_run!("2 >= 2", true);
    assert_run!("2 >= 3", false);
}

#[test]
fn math() {
    assert_run!("1 + 2", 3);
    assert_run!("1 - 2", -1);
    // checked math: i64::MAX + 1
    assert_run!("9223372036854775807 + 1", Value::Void);

    assert_run!("2 * 3", 6);
    assert_run!("6 / 3", 2);

    // Order of operations
    assert_run!("6 * 2 + 4 / 2", 14);
    assert_run!("6 * (2 + 4) / 2", 18);

    // Floating points
    assert_run!("1.1 + 2.0", Value::Real(3.1));
    assert_run!("-1.0 - -10.0", Value::Real(9.));
    assert_run!("-0.0 * 0.0", Value::Real(0.));
}

#[test]
fn assignment() {
    assert_run!(
        r#"
        a := 2
        b := 3
        a * b
    "#,
        6
    );
}

#[derive(Debug, Clone)]
struct TestDynamic(u8);

impl Display for TestDynamic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("TestDynamic")
    }
}

impl DynamicValue for TestDynamic {
    fn is_truthy(&self) -> bool {
        true
    }

    fn kind(&self) -> &'static str {
        "TestDynamic"
    }

    fn call(&mut self, name: &Symbol, _args: PoppedValues<'_>) -> Result<Value, FaultKind> {
        match name.as_ref() {
            "squared" => Ok(Value::dynamic(Self(self.0.pow(2)))),
            _ => Err(FaultKind::Dynamic(DynamicFault::new(format!(
                "unknown function {name}"
            )))),
        }
    }
}

#[test]
fn dynamic_values() {
    // Call the squared function on the passed TestDynamic
    let test = vm::Function {
        arg_count: 1,
        variable_count: 0,
        code: vec![Instruction::CallInstance {
            target: Some(ValueOrSource::Argument(0)),
            name: Symbol::from("squared"),
            arg_count: 0,
            destination: vm::Destination::Stack,
        }],
    };

    // Invoke the function with a TestDynamic value 2, expect 4.
    let mut context = Bud::empty().with_function("test", test);
    let two_squared = context
        .call::<Value, _, _>(&Symbol::from("test"), [Value::dynamic(TestDynamic(2))])
        .unwrap();
    assert_eq!(two_squared.into_dynamic::<TestDynamic>().unwrap().0, 4);

    // Test the various ways to access the embedded type
    let one = Value::dynamic(TestDynamic(1));
    let mut cloned = one.clone();
    cloned.as_dynamic_mut::<TestDynamic>().unwrap().0 = 2;

    assert_eq!(one.as_dynamic::<TestDynamic>().unwrap().0, 1);
    assert_eq!(cloned.as_dynamic::<TestDynamic>().unwrap().0, 2);

    let cloned = one.clone();
    // First into_dynamic will use the clone path
    assert_eq!(one.into_dynamic::<TestDynamic>().unwrap().0, 1);
    // Second into_dynamic will use the Arc::try_unwrap
    assert_eq!(cloned.into_dynamic::<TestDynamic>().unwrap().0, 1);
}

#[test]
fn dynamic_invoke() {
    let mut context = Bud::empty();
    context
        .run_source::<()>(
            r#"
        function test(dynamic)
            dynamic.squared()
        end
    "#,
        )
        .unwrap();
    let result: TestDynamic = context
        .call(&Symbol::from("test"), [Value::dynamic(TestDynamic(2))])
        .unwrap();
    assert_eq!(result.0, 4);
}

#[test]
fn dynamic_error() {
    let mut context = Bud::empty();
    context
        .run_source::<()>(
            r#"
        function test(dynamic)
            dynamic.test()
        end
    "#,
        )
        .unwrap();
    let error = context
        .call::<(), _, _>(&Symbol::from("test"), [Value::dynamic(TestDynamic(2))])
        .unwrap_err();
    match error {
        Error::Fault(Fault {
            kind: FaultOrPause::Fault(FaultKind::Dynamic(dynamic)),
            ..
        }) => {
            let error = dynamic.try_unwrap::<String>().unwrap();
            assert!(error.contains("test"));
        }
        err => unreachable!("unexpected error: {err}"),
    }
}

#[test]
fn strings() {
    // Strings don't do much beyond exist right now
    let string = Bud::empty()
        .run_source::<String>(r#""hello, world!""#)
        .unwrap();
    assert_eq!(string, "hello, world!");
}
