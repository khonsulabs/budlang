use budlang::{
    ast::{self, Call, ExpressionTree, Function, If},
    vm::{Comparison, Symbol},
};

use crate::ast::BinOpKind;

fn main() {
    let mut context = budlang::Bud::empty();
    let code_unit = ast::CodeUnit::new(|builder| {
        vec![builder.call(Call::global("fibonacci", [builder.integer(10)]))]
    })
    .with(
        "fibonacci",
        Function::new(
            "fibonacci",
            vec![Symbol::from("n")],
            ExpressionTree::build(|builder| {
                let n = builder.identifier("n");
                let one = builder.integer(1);
                let two = builder.integer(2);
                builder.if_node(
                    If::new(
                        builder.compare_node(Comparison::LessThanOrEqual, n, two),
                        builder.return_node(one),
                    )
                    .with_else(builder.binop_node(
                        BinOpKind::Add,
                        builder.call(Call::recurse([builder.binop_node(BinOpKind::Sub, n, one)])),
                        builder.call(Call::recurse([builder.binop_node(BinOpKind::Sub, n, two)])),
                    )),
                )
            }),
        ),
    )
    .compile(&mut context)
    .unwrap();

    let result: i64 = code_unit.load_into(&mut context).unwrap();
    assert_eq!(result, 55);
}

#[test]
fn runs() {
    main()
}
