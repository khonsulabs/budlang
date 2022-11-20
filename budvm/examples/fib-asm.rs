use budvm::{ir::Module, VirtualMachine};

fn main() {
    let mut vm = VirtualMachine::empty();
    let module = Module::from_asm(
        r#"
            push 10
            call fibonacci 1 $

            function fibonacci @n
            lte @n 2 jump #if_greater_than_two
            return 1

            #if_greater_than_two
            sub @n 1 $
            recurse 1 $fib_n_minus_1
            sub @n 2 $
            recurse 1 $fib_n_minus_2
            add $fib_n_minus_1 $fib_n_minus_2 $$
        "#,
    )
    .unwrap();
    let result: i64 = module.load_into(&mut vm).unwrap();
    assert_eq!(result, 55);
}

#[test]
fn runs() {
    main()
}
