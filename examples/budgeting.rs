use budlang::{
    vm::{Bud, Budgeted, Fault, FaultKind},
    Error,
};

fn main() {
    // Bud includes a simple Environment that only allows a budgeted number of
    // instructions to operate before pausing. The default budget is 0, which
    // means the script will immediately pause when it begins executing
    // `fibonacci(10)`.
    let mut context = Bud::default_for(Budgeted::default());

    let mut result = context.run_source::<i64>(
        r#"function fibonacci(n)
                if n <= 2
                    1
                else
                    this(n - 1) + this(n - 2)
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
            Err(Error::Fault(Fault {
                kind: FaultKind::Paused(mut paused),
                ..
            })) => {
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
