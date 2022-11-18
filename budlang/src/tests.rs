use std::{fmt::Display, vec};

use crate::{
    parser::{Lexer, TokenKind},
    Bud, Error,
};

use budvm::{
    DynamicFault, DynamicValue, Fault, FaultKind, FaultOrPause, HashMap, Instruction, List,
    PoppedValues, Symbol, Value, ValueOrSource,
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

    fn call(&self, name: &Symbol, _args: &mut PoppedValues<'_>) -> Result<Value, FaultKind> {
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
    let test = budvm::Function {
        name: Symbol::from("test"),
        arg_count: 1,
        variable_count: 0,
        code: vec![Instruction::CallInstance {
            target: Some(ValueOrSource::Argument(0)),
            name: Symbol::from("squared"),
            arg_count: 0,
            destination: budvm::Destination::Stack,
        }],
    };

    // Invoke the function with a TestDynamic value 2, expect 4.
    let mut context = Bud::empty().with_function(test);
    let two_squared = context
        .call::<Value, _, _>(&Symbol::from("test"), [Value::dynamic(TestDynamic(2))])
        .unwrap();
    assert_eq!(two_squared.into_dynamic::<TestDynamic>().unwrap().0, 4);

    // Test the various ways to access the embedded type
    let one = Value::dynamic(TestDynamic(1));

    let cloned = one.clone();
    // We cannot unwrap either value until one is dropped. This step drops
    // `clone` because into_dynamic takes the value, then returns it into an
    // error which is being dropped.
    assert!(cloned.try_into_dynamic::<TestDynamic>().is_err());
    // Now we can retrieve the inner value of one.
    assert_eq!(one.into_dynamic::<TestDynamic>().unwrap().0, 1);
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
        Fault {
            kind: FaultOrPause::Fault(FaultKind::Dynamic(dynamic)),
            ..
        } => {
            let error = dynamic.try_unwrap::<String>().unwrap();
            assert!(error.contains("test"));
        }
        err => unreachable!("unexpected error: {err}"),
    }
}

#[test]
fn strings() {
    let string = Bud::empty()
        .run_source::<String>(r#""hello" + ", world!""#)
        .unwrap();
    assert_eq!(string, "hello, world!");
    let repeated = Bud::empty().run_source::<String>(r#""a" * 5"#).unwrap();
    assert_eq!(repeated, "aaaaa");
    // Test reverse ops, where DynamicValue::checked_mul is invoked with
    // is_reverse = true.
    let repeated = Bud::empty().run_source::<String>(r#"5 * "a""#).unwrap();
    assert_eq!(repeated, "aaaaa");

    // TODO this should be able to be "literal".replace(), but we currently
    // don't support invoking on a literal.
    let replaced = Bud::empty()
        .run_source::<String>(
            r#"
                a := "abcda"
                a.replace("a", "1")
            "#,
        )
        .unwrap();
    assert_eq!(replaced, "1bcd1");
}

#[test]
fn maps() {
    let map = Bud::empty()
        .run_source::<HashMap>(r#"{"hello": "world", 2: 42}"#)
        .unwrap();
    assert_eq!(map.len(), 2);
    assert_eq!(
        map.get(&Value::dynamic(String::from("hello"))),
        Some(Value::dynamic(String::from("world")))
    );
    assert_eq!(map.get(&Value::Integer(2)), Some(Value::Integer(42)));

    // Floats aren't hashable
    assert!(matches!(
        Bud::empty()
            .run_source::<HashMap>(r#"{3.2: 1, }"#)
            .unwrap_err(),
        Error::Vm(budvm::Error::Fault(Fault {
            kind: FaultOrPause::Fault(FaultKind::ValueCannotBeHashed(Value::Real(_))),
            ..
        }))
    ));
    let map = dbg!(Bud::empty()
        .run_source::<HashMap>(
            r#"
                a := {1: true}
                a.insert(2, false)
                a.insert(3, a.get(1))
                a.insert(4, a.remove(2))
                a
            "#,
        )
        .unwrap());
    assert_eq!(map.get(&Value::Integer(1)), Some(Value::Boolean(true)));
    assert_eq!(map.get(&Value::Integer(2)), None);
    assert_eq!(map.get(&Value::Integer(3)), Some(Value::Boolean(true)));
    assert_eq!(map.get(&Value::Integer(4)), Some(Value::Boolean(false)));
}

#[test]
fn lists() {
    let list = Bud::empty()
        .run_source::<List>(r#"[1, 2, 3]"#)
        .unwrap()
        .into_inner();
    assert_eq!(list.len(), 3);
    assert_eq!(list[0], Value::Integer(1));
    assert_eq!(list[1], Value::Integer(2));
    assert_eq!(list[2], Value::Integer(3));
    let list = Bud::empty()
        .run_source::<List>(
            r#"
                a := []
                a.push(2)
                a.push(3)
                a.push_front(1)

                a.push_front(0)
                a.push_front(-1)
                a.push(5)
                b := a.remove(1) + a.pop() + a.pop_front()
                a.push(b)

                a
            "#,
        )
        .unwrap();
    assert_eq!(list.len(), 4);
    assert_eq!(list.get(0).unwrap(), Value::Integer(1));
    assert_eq!(list.get(1).unwrap(), Value::Integer(2));
    assert_eq!(list.get(2).unwrap(), Value::Integer(3));
    assert_eq!(list.get(3).unwrap(), Value::Integer(4)); // adds -1, 5, and 0
}

#[test]
fn interactive() {
    // Test variable persistence
    let mut session = Bud::empty();
    session.evaluate::<()>("a := 42").unwrap();
    assert_eq!(session.evaluate::<i64>("a").unwrap(), 42);

    // Test a new function calling an existing function
    session
        .evaluate::<()>(
            r#"
                function foo()
                    42
                end
            "#,
        )
        .unwrap();
    session
        .evaluate::<()>(
            r#"
                function bar()
                    foo()
                end
            "#,
        )
        .unwrap();
    assert_eq!(session.evaluate::<i64>("bar()").unwrap(), 42);
}

#[test]
fn loops() {
    // Basic loop with continue and break usage
    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                a := 0
                total := 0
                loop
                    a := a + 1
                    if a = 5
                        break total
                    else
                        if a = 3
                            continue
                        end
                    end
                    total := total + a
                end
            "#,
        )
        .unwrap();
    assert_eq!(result, 1 + 2 + 4);

    // Test labeled break
    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                a := 1
                loop #infinite
                    loop
                        if a = 10
                            break #infinite a
                        else
                            a := a + 1
                        end
                    end
                end
            "#,
        )
        .unwrap();
    assert_eq!(result, 10);

    // Test labeled continue
    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                b := 0
                c := 0
                loop #outer
                    if b = 10
                        break c
                    end
                    b := b + 1
                    a := 0
                    loop
                        if a = 10
                            continue #outer
                        end
                        a := a + 1
                        c := c + 1
                        continue
                    end
                end
            "#,
        )
        .unwrap();
    assert_eq!(result, 100);
}

#[test]
fn conditioned_loops() {
    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                a := 0
                loop while a < 10
                    a := a + 1
                end
                a
            "#,
        )
        .unwrap();
    assert_eq!(result, 10);

    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                a := 0
                loop until a = 10
                    a := a + 1
                end
                a
            "#,
        )
        .unwrap();
    assert_eq!(result, 10);
}

#[test]
fn for_loops() {
    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                sum := 0
                loop for x := 0 to 5
                    sum := sum + x
                end
                sum
            "#,
        )
        .unwrap();
    assert_eq!(result, 1 + 2 + 3 + 4);
    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                sum := 0
                loop for x := 0 to 5 inclusive
                    sum := sum + x
                end
                sum
            "#,
        )
        .unwrap();
    assert_eq!(result, 1 + 2 + 3 + 4 + 5);
    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                sum := 0
                loop for x := 5 down to 1
                    sum := sum + x
                end
                sum
            "#,
        )
        .unwrap();
    assert_eq!(result, 5 + 4 + 3 + 2);
    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                sum := 0
                loop for x := 5 down to 1 inclusive
                    sum := sum + x
                end
                sum
            "#,
        )
        .unwrap();
    assert_eq!(result, 5 + 4 + 3 + 2 + 1);
}

#[test]
fn nesting_if() {
    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                if (if 1
                        true
                    end)
                    42
                end
            "#,
        )
        .unwrap();
    assert_eq!(result, 42);
}

#[test]
fn comments() {
    let parsed = Lexer::new("// test")
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    assert_eq!(parsed.len(), 1);
    match &parsed[0].kind {
        TokenKind::Comment(comment) => {
            assert_eq!(comment, "// test");
        }
        _ => unreachable!("unexpected token kind"),
    }

    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                // comment alone on line
                if true // comment after if line
                    a := 2 // comment after expression
                    loop // comment after loop
                        break // comment after break
                    end
                    1
                end // comment after end
            "#,
        )
        .unwrap();
    assert_eq!(result, 1);
}

#[test]
fn nested_assignments() {
    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                a := b := 4
                a * b
            "#,
        )
        .unwrap();
    assert_eq!(result, 16);
}

#[test]
fn if_else_if() {
    let result = Bud::empty()
        .run_source::<i64>(
            r#"
                function test(a)
                    if a = 0
                        2
                    else if a = 1
                        3
                    else
                        4
                    end
                end

                test(0) + test(1) + test(2)
            "#,
        )
        .unwrap();
    assert_eq!(result, 9);
}

#[test]
fn logic() {
    // To verify short circuit behavior, we have register a native function that
    // panics when called.
    let mut bud = Bud::empty()
        .with_native_function("unreachable", |_args: &mut PoppedValues<'_>| {
            unreachable!("short circuit failed")
        });

    assert!(!bud
        .run_source::<bool>(r#"false and unreachable()"#,)
        .unwrap());
    assert!(bud.run_source::<bool>(r#"true and true"#,).unwrap());
    assert!(!bud.run_source::<bool>(r#"true and false"#,).unwrap());

    assert!(bud.run_source::<bool>(r#"true or unreachable()"#,).unwrap());
    assert!(bud.run_source::<bool>(r#"false or true"#,).unwrap());
    assert!(bud.run_source::<bool>(r#"false or false"#,).unwrap());

    assert!(!bud.run_source::<bool>(r#"false xor false"#,).unwrap());
    assert!(!bud.run_source::<bool>(r#"true xor true"#,).unwrap());
    assert!(bud.run_source::<bool>(r#"true xor false"#,).unwrap());
    assert!(bud.run_source::<bool>(r#"false xor true"#,).unwrap());

    assert!(!bud.run_source::<bool>(r#"not true"#,).unwrap());
    assert!(bud.run_source::<bool>(r#"not false"#,).unwrap());
    assert_eq!(bud.run_source::<i64>(r#"not 0"#,).unwrap(), !0);
    assert!(bud.run_source::<bool>(r#"not 0.0"#,).unwrap());
    assert!(bud.run_source::<bool>(r#"not """#,).unwrap());

    assert!(bud
        .run_source::<bool>(
            r#"
                a := false
                not a
            "#,
        )
        .unwrap());
    assert_eq!(
        bud.run_source::<i64>(
            r#"
                a := 0
                not a
            "#,
        )
        .unwrap(),
        !0
    );
    assert!(bud
        .run_source::<bool>(
            r#"
                a := 0.0
                not a
            "#,
        )
        .unwrap());
    assert!(bud
        .run_source::<bool>(
            r#"
                    a := ""
                    not a
                "#,
        )
        .unwrap());

    // Verify that this groups `(not true) and true` instead of `not (true and true)`.
    assert!(!bud.run_source::<bool>(r#"not true and true"#,).unwrap());
}

#[test]
fn bitwise() {
    assert_run!("1 & 3", 1);
    assert_run!("1 | 3", 3);
    assert_run!("1 ^ 3", 2);

    // Test coersion to logic. These operators won't short circuit, but they
    // behave consistently by truncating to boolean operations when non-integer
    // types are mixed.
    assert_run!("1 & false", false);
    assert_run!("1 | false", true);
    assert_run!("1 ^ true", false);
}
