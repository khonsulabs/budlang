use crate::vm::{Context, Value};

macro_rules! assert_run {
    ($source:literal, $result:expr) => {
        let mut context = Context::empty();
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
}
