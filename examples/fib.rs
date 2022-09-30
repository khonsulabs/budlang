use budlang::vm;

fn main() {
    let mut context = vm::Context::empty();
    let result: i64 = context
        .run_source(
            r#"
    function fibonacci(n)
        if n <= 2
            1
        else
            fibonacci(n - 1) + fibonacci(n - 2)
        end
    end

    fibonacci(35)
"#,
        )
        .unwrap();
    assert_eq!(result, 9227465);
}

#[test]
fn runs() {
    main()
}
