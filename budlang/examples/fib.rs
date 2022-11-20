use budlang::Bud;

fn main() {
    let mut context = Bud::empty();
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

                fibonacci(10)
            "#,
        )
        .unwrap();
    assert_eq!(result, 55);
}

#[test]
fn runs() {
    main()
}
