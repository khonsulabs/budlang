use budvm::{ir::Module, VirtualMachine};

fn main() {
    let mut vm = VirtualMachine::empty();
    let module = Module::from_asm(
        r#"
            // Any loose assembly before function calls will be gathered into
            // the module's init function, which will be executed when the
            // module is loaded into a virtual machine.
            //
            // The init function in this case calls the fibonacci function with
            // 1 argument: 10.
            push 10
            call fibonacci 1 $

            // Define the recursive fibonacci function with one parameter, @n
            function fibonacci @n
            // If @n is less than 2 or equal to 2, return 1
            lte @n 2 jump #if_greater_than_two
            return 1

            // Otherwise, recurse twice, passing in n-1 and n-2, and then sum
            // the results.
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
