use budlang::{
    vm::{self, Budgeted, Fault, FaultOrPause},
    Bud, Error,
};

fn main() {
    // Bud includes a simple Environment that only allows a budgeted number of
    // instructions to operate before pausing. The default budget is 0, which
    // means the script will immediately pause when it begins executing
    // `fibonacci(10)`.
    let mut context = Bud::default_for(Budgeted::empty());

    let mut result = context.run_source::<i64>(
        r#"function fibonacci(n)
                if n <= 2
                    1
                else
                    fibonacci(n - 1) + fibonacci(n - 2)
                end
           end

           fibonacci(10)
        "#,
    );

    let mut total_budget_allocated = 0;
    loop {
        match result {
            Ok(result) => {
                let budget_spent = total_budget_allocated - context.environment().balance();
                println!("Total instructions performed: {budget_spent}");
                assert_eq!(result, 55);
                break;
            }
            Err(Error::Vm(vm::Error::Fault(Fault {
                kind: FaultOrPause::Pause(mut paused),
                ..
            }))) => {
                println!("Ran out of budget. Allowing 10 more operations");
                paused.environment_mut().add_budget(10);
                total_budget_allocated += 10;
                result = paused.resume().map_err(Error::from);
            }
            Err(other) => unreachable!("Error executing: {other}"),
        };
    }
}

#[test]
fn runs() {
    main()
}
