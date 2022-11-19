#![allow(missing_docs, clippy::missing_panics_doc)] // TODO docs and panics for ast

use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::{Debug, Display},
};

use budvm::{
    ir::{
        self, CodeBlockBuilder, CompareAction, Destination, Instruction, Label, LinkError, Literal,
        LiteralOrSource, LoopScope, Module, Scope, ScopeSymbol, ScopeSymbolKind,
    },
    Comparison, Intrinsic, OptionalSymbol, Symbol,
};

pub struct ExpressionTree {
    nodes: Vec<Node>,
    root: NodeId,
}

impl ExpressionTree {
    pub fn build(init: impl FnOnce(&mut SyntaxTreeBuilder) -> NodeId) -> Self {
        let mut builder = SyntaxTreeBuilder::new();
        let root = init(&mut builder);
        builder.finish(root)
    }

    fn node(&self, id: NodeId) -> &Node {
        self.nodes.get(id.0).expect("invalid node id")
    }

    fn root(&self) -> &Node {
        self.node(self.root)
    }

    pub fn generate_code(&self, block: &mut CodeBlockBuilder) -> Result<(), CompilationError> {
        self.root().generate_code(Destination::Return, block, self)
    }
}

impl Debug for ExpressionTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ExpressionTree")
            .field(&ExpressionTreeNode {
                tree: self,
                id: self.root,
            })
            .finish()
    }
}

#[derive(Debug, Clone, Copy)]
#[must_use]
pub struct NodeId(usize);

struct ExpressionTreeNode<'a> {
    tree: &'a ExpressionTree,
    id: NodeId,
}
impl<'a> ExpressionTreeNode<'a> {
    fn node(&self, id: NodeId) -> Self {
        Self {
            tree: self.tree,
            id,
        }
    }
}

impl<'a> Debug for ExpressionTreeNode<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.tree.node(self.id) {
            Node::If(if_op) => f
                .debug_struct("If")
                .field("condition", &self.node(if_op.condition))
                .field("if_true", &self.node(if_op.true_block))
                .field("else", &if_op.else_block.map(|node| self.node(node)))
                .finish(),
            Node::BinOp(binop) => f
                .debug_struct("BinOp")
                .field("kind", &binop.kind)
                .field("left", &self.node(binop.left))
                .field("right", &self.node(binop.right))
                .finish(),
            Node::Not(op) => f
                .debug_struct("Not")
                .field("expr", &self.node(op.expr))
                .finish(),
            Node::Assign(assign) => f
                .debug_struct("Assign")
                .field("target", &self.node(assign.target))
                .field("value", &self.node(assign.value))
                .finish(),
            Node::Map(map) => {
                let mut dbg = f.debug_tuple("Map");
                for mapping in &map.mappings {
                    dbg.field(&(self.node(mapping.key), self.node(mapping.value)));
                }
                dbg.finish()
            }
            Node::List(list) => {
                let mut dbg = f.debug_tuple("List");
                for value in &list.values {
                    dbg.field(&self.node(*value));
                }
                dbg.finish()
            }
            Node::Loop(l) => f
                .debug_struct("Loop")
                .field("body", &self.node(l.body))
                .finish(),
            // Node::Lookup(lookup) => f
            //     .debug_struct("Lookup")
            //     .field("base", &self.node(lookup.base))
            //     .field("name", &lookup.name)
            //     .finish(),
            Node::Block(block) => {
                let mut list = f.debug_list();
                for statement in &block.0 {
                    list.entry(&self.node(*statement));
                }
                list.finish()
            }
            Node::Literal(literal) => Debug::fmt(literal, f),
            Node::Identifier(identifier) => Debug::fmt(identifier, f),
            Node::Call(call) => {
                let target = call.target.map(|node| self.node(node));
                let name = if let Some(symbol) = &call.name {
                    symbol.as_ref()
                } else {
                    "this"
                };
                let args = call
                    .args
                    .iter()
                    .map(|node| self.node(*node))
                    .collect::<Vec<_>>();
                f.debug_struct("Call")
                    .field("target", &target)
                    .field("name", &name)
                    .field("args", &&args[..])
                    .finish()
            }
            Node::Return(value) => {
                let value = self.node(*value);
                f.debug_struct("Return").field("value", &value).finish()
            }
            Node::Break(value) => {
                let mut s = f.debug_struct("Break");
                if let Some(name) = &value.name {
                    s.field("name", name);
                }
                if let Some(value) = value.value {
                    s.field("result", &self.node(value));
                }
                s.finish()
            }
            Node::Continue(value) => {
                let mut s = f.debug_struct("Continue");
                if let Some(name) = &value.name {
                    s.field("name", name);
                }
                s.finish()
            }
        }
    }
}

#[derive(Debug)]
enum Node {
    If(If),
    BinOp(BinOp),
    Not(Not), // Upgrade to UnaryOp if we add more
    Assign(Assign),
    // UnaryOp(UnaryOp),
    Block(Block),
    Literal(Literal),
    Identifier(Symbol),
    Map(Map),
    List(List),
    // Lookup(Lookup),
    Call(Call),
    Return(NodeId),
    Loop(Loop),
    Break(Break),
    Continue(Continue),
}

impl Node {
    pub fn generate_code(
        &self,
        result: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        match self {
            Node::If(if_expr) => if_expr.generate_code(result, operations, tree),
            Node::BinOp(bin_op) => bin_op.generate_code(result, operations, tree),
            Node::Not(not) => not.generate_code(result, operations, tree),
            Node::Block(statements) => {
                let mut last_result_var = None;
                for statement in &statements.0 {
                    let statement = tree.node(*statement);
                    let result = operations.new_temporary_variable();
                    statement.generate_code(Destination::Variable(result), operations, tree)?;
                    last_result_var = Some(result);
                }
                if let Some(last_result) = last_result_var {
                    operations
                        .store_into_destination(LiteralOrSource::Variable(last_result), result);
                }
                Ok(())
            }
            Node::Assign(assign) => assign.generate_code(result, operations, tree),
            Node::Literal(literal) => {
                operations
                    .store_into_destination(LiteralOrSource::Literal(literal.clone()), result);
                Ok(())
            }
            Node::Identifier(identifier) => operations
                .load_from_symbol(identifier, result)
                .map_err(CompilationError::from),
            Node::Map(map) => map.generate_code(result, operations, tree),
            Node::List(list) => list.generate_code(result, operations, tree),
            // Node::Lookup(lookup) => lookup.generate_code(operations, tree),
            Node::Call(call) => call.generate_code(result, operations, tree),
            Node::Return(value) => Self::generate_return(*value, operations, tree),
            Node::Loop(l) => l.generate_code(result, operations, tree),
            Node::Break(l) => l.generate_code(result, operations, tree),
            Node::Continue(l) => l.generate_code(result, operations, tree),
        }
    }

    pub fn to_value_or_source(
        &self,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<LiteralOrSource, CompilationError> {
        match self {
            Node::Literal(literal) => Ok(LiteralOrSource::Literal(literal.clone())),
            Node::Identifier(identifier) => match operations.lookup(identifier) {
                Some(ScopeSymbol::Argument(arg)) => Ok(LiteralOrSource::Argument(*arg)),
                Some(ScopeSymbol::Variable(var)) => Ok(LiteralOrSource::Variable(*var)),
                Some(ScopeSymbol::Function { .. }) => todo!("attempt to take function as value"),
                None => Err(CompilationError::UndefinedIdentifier(identifier.clone())),
            },
            // Node::Lookup(lookup) => lookup.generate_code(operations, tree),
            // Node::Call(call) => call.generate_code(result, operations, tree),
            // Node::Return(value) => {
            //     Self::generate_return(*value, operations, tree);
            // }
            _ => {
                let variable = operations.new_temporary_variable();
                self.generate_code(Destination::Variable(variable), operations, tree)?;
                Ok(LiteralOrSource::Variable(variable))
            }
        }
    }

    fn generate_return(
        value_to_return: NodeId,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        let value_to_return = tree.node(value_to_return);
        value_to_return.generate_code(Destination::Return, operations, tree)?;
        Ok(())
    }
}

#[derive(Debug)]
pub struct If {
    condition: NodeId,
    true_block: NodeId,
    else_block: Option<NodeId>,
}

impl If {
    #[must_use]
    pub fn new(condition: NodeId, true_block: NodeId) -> Self {
        Self {
            condition,
            true_block,
            else_block: None,
        }
    }

    #[must_use]
    pub fn with_else(mut self, else_block: NodeId) -> Self {
        self.else_block = Some(else_block);
        self
    }

    fn generate_code(
        &self,
        result: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        let condition = tree.node(self.condition);
        let after_false_label = operations.new_label();
        let if_false_label = self.else_block.map(|_| operations.new_label());
        let false_jump_to = if_false_label.unwrap_or(after_false_label);
        if let Node::BinOp(BinOp {
            kind: BinOpKind::Compare(comparison),
            left,
            right,
        }) = condition
        {
            // The if statement is a result of the comparison. Use the special
            // form of the comparison operator to branch instead of using an if
            // operation
            let left = tree.node(*left).to_value_or_source(operations, tree)?;
            let right = tree.node(*right).to_value_or_source(operations, tree)?;
            operations.push(Instruction::Compare {
                comparison: *comparison,
                left,
                right,
                action: CompareAction::JumpIfFalse(false_jump_to),
            });
        } else {
            // The if statement is a result of something more complex
            let condition_result = operations.new_temporary_variable();
            condition.generate_code(Destination::Variable(condition_result), operations, tree)?;
            operations.push(Instruction::If {
                condition: LiteralOrSource::Variable(condition_result),
                false_jump_to,
            });
        }
        let true_block = tree.node(self.true_block);
        true_block.generate_code(result, operations, tree)?;
        if let (Some(else_block), Some(if_false_label)) = (self.else_block, if_false_label) {
            operations.push(Instruction::JumpTo(after_false_label));
            operations.label(if_false_label);
            let else_block = tree.node(else_block);
            else_block.generate_code(result, operations, tree)?;
        }
        operations.label(after_false_label);
        Ok(())
    }
}

#[derive(Debug)]
pub struct Block(Vec<NodeId>);

#[derive(Debug)]
pub struct BinOp {
    kind: BinOpKind,
    left: NodeId,
    right: NodeId,
}

impl BinOp {
    fn generate_code(
        &self,
        result: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        self.kind
            .generate_code(self.left, self.right, result, operations, tree)
    }
}

#[derive(Debug)]
pub enum BinOpKind {
    Add,
    Sub,
    Multiply,
    Divide,
    LogicalAnd,
    LogicalOr,
    LogicalXor,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    ShiftLeft,
    ShiftRight,
    Compare(Comparison),
}

impl BinOpKind {
    fn generate_code(
        &self,
        left: NodeId,
        right: NodeId,
        destination: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        let left = tree.node(left);
        let right = tree.node(right);
        let left = left.to_value_or_source(operations, tree)?;

        if matches!(self, BinOpKind::LogicalAnd | BinOpKind::LogicalOr) {
            // These operators short circuit, so we delay evaluating right until
            // we've checked the left.
            self.generate_short_circuit_op(left, right, destination, operations, tree)?;
        } else {
            // None of these operators short circuit, so we can evaluate right
            // immediately.
            let right = right.to_value_or_source(operations, tree)?;
            match self {
                BinOpKind::Add => operations.push(Instruction::Add {
                    left,
                    right,
                    destination,
                }),
                BinOpKind::Sub => operations.push(Instruction::Sub {
                    left,
                    right,
                    destination,
                }),
                BinOpKind::Multiply => operations.push(Instruction::Multiply {
                    left,
                    right,
                    destination,
                }),
                BinOpKind::Divide => operations.push(Instruction::Divide {
                    left,
                    right,
                    destination,
                }),
                BinOpKind::BitwiseAnd => operations.push(Instruction::BitwiseAnd {
                    left,
                    right,
                    destination,
                }),
                BinOpKind::BitwiseOr => operations.push(Instruction::BitwiseOr {
                    left,
                    right,
                    destination,
                }),
                BinOpKind::LogicalXor => {
                    operations.push(Instruction::LogicalXor {
                        left,
                        right,
                        destination,
                    });
                }
                BinOpKind::BitwiseXor => {
                    operations.push(Instruction::BitwiseXor {
                        left,
                        right,
                        destination,
                    });
                }
                BinOpKind::ShiftLeft => {
                    operations.push(Instruction::ShiftLeft {
                        left,
                        right,
                        destination,
                    });
                }
                BinOpKind::ShiftRight => {
                    operations.push(Instruction::ShiftRight {
                        left,
                        right,
                        destination,
                    });
                }
                BinOpKind::Compare(comparison) => operations.push(Instruction::Compare {
                    comparison: *comparison,
                    left,
                    right,
                    action: CompareAction::Store(destination),
                }),
                BinOpKind::LogicalAnd | BinOpKind::LogicalOr => {
                    unreachable!("short circuit binops are handled elsewhere")
                }
            }
        }

        Ok(())
    }
    fn generate_short_circuit_op(
        &self,
        left: LiteralOrSource,
        right: &Node,
        destination: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        let after_op = operations.new_label();
        match self {
            BinOpKind::LogicalAnd => {
                let store_false = operations.new_label();
                operations.push(Instruction::If {
                    condition: left,
                    false_jump_to: store_false,
                });
                // If left was false, we jump over the evaluation of right.
                let right = right.to_value_or_source(operations, tree)?;
                operations.push(Instruction::If {
                    condition: right,
                    false_jump_to: store_false,
                });
                operations.store_into_destination(
                    LiteralOrSource::Literal(Literal::Boolean(true)),
                    destination,
                );
                operations.push(Instruction::JumpTo(after_op));

                operations.label(store_false);
                operations.store_into_destination(
                    LiteralOrSource::Literal(Literal::Boolean(false)),
                    destination,
                );
            }
            BinOpKind::LogicalOr => {
                let check_right = operations.new_label();
                let store_true = operations.new_label();
                operations.push(Instruction::If {
                    condition: left,
                    false_jump_to: check_right,
                });
                // If left was true, we already know we're good
                operations.push(Instruction::JumpTo(store_true));

                operations.label(check_right);
                let right = right.to_value_or_source(operations, tree)?;
                let store_false = operations.new_label();
                operations.push(Instruction::If {
                    condition: right,
                    false_jump_to: store_false,
                });

                operations.label(store_true);
                operations.store_into_destination(
                    LiteralOrSource::Literal(Literal::Boolean(true)),
                    destination,
                );
                operations.push(Instruction::JumpTo(after_op));

                operations.label(store_false);
                operations.store_into_destination(
                    LiteralOrSource::Literal(Literal::Boolean(true)),
                    destination,
                );
            }
            _ => unreachable!("pre-matched above"),
        }
        operations.label(after_op);
        Ok(())
    }
}

#[derive(Debug)]
pub struct Not {
    expr: NodeId,
}

impl Not {
    fn generate_code(
        &self,
        result: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        match tree.node(self.expr) {
            Node::Literal(literal) => {
                let expr = LiteralOrSource::Literal(match literal {
                    Literal::Void => Literal::Boolean(true),
                    Literal::Integer(value) => Literal::Integer(!value),
                    Literal::Real(value) => Literal::Boolean(value.abs() < f64::EPSILON),
                    Literal::Boolean(value) => Literal::Boolean(!value),
                    Literal::String(value) => Literal::Boolean(value.is_empty()),
                });
                operations.store_into_destination(expr, result);
            }
            other => {
                let expr = operations.new_temporary_variable();
                other.generate_code(Destination::Variable(expr), operations, tree)?;
                operations.push(Instruction::Not {
                    value: LiteralOrSource::Variable(expr),
                    destination: result,
                });
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct Call {
    target: Option<NodeId>,
    name: Option<Symbol>,
    args: Vec<NodeId>,
}

impl Call {
    pub fn recurse<Args: IntoIterator<Item = NodeId>>(args: Args) -> Self {
        Self {
            target: None,
            name: None,
            args: args.into_iter().collect(),
        }
    }

    pub fn global<Args: IntoIterator<Item = NodeId>>(name: impl Into<Symbol>, args: Args) -> Self {
        Self {
            target: None,
            name: Some(name.into()),
            args: args.into_iter().collect(),
        }
    }

    pub fn on<Args: IntoIterator<Item = NodeId>>(
        target: NodeId,
        name: impl Into<Symbol>,
        args: Args,
    ) -> Self {
        Self {
            target: Some(target),
            name: Some(name.into()),
            args: args.into_iter().collect(),
        }
    }

    fn generate_code(
        &self,
        destination: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        match (self.target, self.name.as_ref()) {
            (None, None) => {
                // Recursive call
                for &arg in &self.args {
                    let arg = tree.node(arg);
                    arg.generate_code(Destination::Stack, operations, tree)?;
                }

                operations.push(Instruction::Call {
                    function: None,
                    arg_count: self.args.len(),
                    destination,
                });
            }
            (None, Some(symbol)) => {
                // Global call
                for &arg in &self.args {
                    let arg = tree.node(arg);
                    arg.generate_code(Destination::Stack, operations, tree)?;
                }

                match operations.lookup(symbol) {
                    Some(ScopeSymbol::Argument(_) | ScopeSymbol::Variable(_)) => {
                        todo!("calling a lambda function in an argument")
                    }
                    Some(ScopeSymbol::Function(function)) => {
                        operations.push(Instruction::Call {
                            function: Some(function.clone()),
                            arg_count: self.args.len(),
                            destination,
                        });
                    }
                    None => operations.push(Instruction::Call {
                        function: Some(symbol.clone()),
                        arg_count: self.args.len(),
                        destination,
                    }),
                }
            }
            (Some(target), Some(name)) => {
                // Evaluate the target expression
                let target = tree.node(target);
                let target = if let Node::Identifier(name) = target {
                    match operations.lookup(name) {
                        Some(ScopeSymbol::Argument(arg)) => LiteralOrSource::Argument(*arg),
                        Some(ScopeSymbol::Variable(var)) => LiteralOrSource::Variable(*var),
                        Some(ScopeSymbol::Function { .. }) => todo!("can't invoke on a function"),
                        None => todo!("unknown identifier"),
                    }
                } else {
                    let target_result = operations.new_temporary_variable();
                    target.generate_code(Destination::Variable(target_result), operations, tree)?;
                    LiteralOrSource::Variable(target_result)
                };

                // Push the arguments
                for &arg in &self.args {
                    let arg = tree.node(arg);
                    arg.generate_code(Destination::Stack, operations, tree)?;
                }

                // Invoke the call
                operations.push(Instruction::CallInstance {
                    target: Some(target),
                    name: name.clone(),
                    arg_count: self.args.len(),
                    destination,
                });
            }
            (Some(_), None) => todo!("invalid instruction"),
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct Assign {
    target: NodeId,
    value: NodeId,
}

impl Assign {
    fn generate_code(
        &self,
        result: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        match tree.node(self.target) {
            Node::Identifier(name) => {
                let variable = operations.variable_index_from_name(name);
                let value = tree.node(self.value);
                value.generate_code(Destination::Variable(variable), operations, tree)?;
                operations.store_into_destination(LiteralOrSource::Variable(variable), result);
            }
            _ => todo!("not a variable name"),
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Map {
    pub mappings: Vec<Mapping>,
}

impl Map {
    fn generate_code(
        &self,
        result: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        for mapping in &self.mappings {
            tree.node(mapping.key)
                .generate_code(Destination::Stack, operations, tree)?;
            tree.node(mapping.value)
                .generate_code(Destination::Stack, operations, tree)?;
        }

        operations.push(Instruction::CallIntrinsic {
            intrinsic: Intrinsic::NewMap,
            arg_count: self.mappings.len() * 2,
            destination: result,
        });
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Mapping {
    pub key: NodeId,
    pub value: NodeId,
}

#[derive(Debug, Clone)]
pub struct List {
    pub values: Vec<NodeId>,
}

impl List {
    fn generate_code(
        &self,
        result: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        for value in &self.values {
            tree.node(*value)
                .generate_code(Destination::Stack, operations, tree)?;
        }

        operations.push(Instruction::CallIntrinsic {
            intrinsic: Intrinsic::NewList,
            arg_count: self.values.len(),
            destination: result,
        });
        Ok(())
    }
}

#[derive(Debug)]
pub struct Loop {
    pub name: Option<Symbol>,
    pub parameters: Option<LoopParameters>,
    pub body: NodeId,
}

impl Loop {
    fn generate_code(
        &self,
        result: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        let mut scope = operations.begin_loop(self.name.clone(), result);

        let continue_label = scope.continue_label;
        let break_label = scope.break_label;

        match &self.parameters {
            Some(LoopParameters::Until(expr)) => {
                Self::generate_until_preamble(*expr, break_label, &mut scope, tree)?;
            }
            Some(LoopParameters::While(expr)) => {
                Self::generate_while_preamble(*expr, break_label, &mut scope, tree)?;
            }
            Some(LoopParameters::For {
                var_name,
                initial_value,
                stop_value,
                step,
                ascending,
                inclusive,
            }) => {
                // Initialize the variable
                let variable = scope.variable_index_from_name(var_name);
                if let Some(initial_value) = *initial_value {
                    tree.node(initial_value).generate_code(
                        Destination::Variable(variable),
                        &mut scope,
                        tree,
                    )?;
                }

                // On the first pass, we skip executing the step instructions
                let after_step = scope.new_label();
                scope.push(Instruction::JumpTo(after_step));

                // We evaluate the value of the step once at the start of the loop, not on each iteration.

                let stop_value = match tree.node(*stop_value) {
                    Node::Literal(literal) => LiteralOrSource::Literal(literal.clone()),
                    other => {
                        let stop_result = scope.new_temporary_variable();
                        other.generate_code(
                            Destination::Variable(stop_result),
                            &mut scope,
                            tree,
                        )?;
                        LiteralOrSource::Variable(stop_result)
                    }
                };

                let step = if let Some(step) = step {
                    let step_result = scope.new_temporary_variable();
                    tree.node(*step).generate_code(
                        Destination::Variable(step_result),
                        &mut scope,
                        tree,
                    )?;
                    LiteralOrSource::Variable(step_result)
                } else if *ascending {
                    LiteralOrSource::Literal(Literal::Integer(1))
                } else {
                    LiteralOrSource::Literal(Literal::Integer(-1))
                };

                // Loop body
                scope.label_continue();
                // Step
                scope.push(Instruction::Add {
                    left: LiteralOrSource::Variable(variable),
                    right: step,
                    destination: Destination::Variable(variable),
                });
                scope.label(after_step);

                // Condition check
                match (*inclusive, *ascending) {
                    (true, true) => scope.push(Instruction::Compare {
                        comparison: Comparison::GreaterThanOrEqual,
                        left: stop_value,
                        right: LiteralOrSource::Variable(variable),
                        action: CompareAction::JumpIfFalse(break_label),
                    }),
                    (true, false) => scope.push(Instruction::Compare {
                        comparison: Comparison::LessThanOrEqual,
                        left: stop_value,
                        right: LiteralOrSource::Variable(variable),
                        action: CompareAction::JumpIfFalse(break_label),
                    }),
                    (false, true) => scope.push(Instruction::Compare {
                        comparison: Comparison::LessThan,
                        left: LiteralOrSource::Variable(variable),
                        right: stop_value,
                        action: CompareAction::JumpIfFalse(break_label),
                    }),
                    (false, false) => scope.push(Instruction::Compare {
                        comparison: Comparison::GreaterThan,
                        left: LiteralOrSource::Variable(variable),
                        right: stop_value,
                        action: CompareAction::JumpIfFalse(break_label),
                    }),
                }
            }
            None => {
                scope.label_continue();
            }
        }

        let body = tree.node(self.body);
        body.generate_code(result, &mut scope, tree)?;
        scope.push(Instruction::JumpTo(continue_label));
        scope.label_break();

        Ok(())
    }

    fn generate_until_preamble(
        condition: NodeId,
        break_label: Label,
        scope: &mut LoopScope<'_, CodeBlockBuilder>,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        scope.label_continue();

        let condition_result = scope.new_temporary_variable();
        let continue_evaluation = scope.new_label();
        tree.node(condition)
            .generate_code(Destination::Variable(condition_result), scope, tree)?;
        scope.push(Instruction::If {
            condition: LiteralOrSource::Variable(condition_result),
            false_jump_to: continue_evaluation,
        });
        scope.push(Instruction::JumpTo(break_label));

        scope.label(continue_evaluation);
        Ok(())
    }

    fn generate_while_preamble(
        condition: NodeId,
        break_label: Label,
        scope: &mut LoopScope<'_, CodeBlockBuilder>,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        scope.label_continue();

        let condition_result = scope.new_temporary_variable();
        tree.node(condition)
            .generate_code(Destination::Variable(condition_result), scope, tree)?;
        scope.push(Instruction::If {
            condition: LiteralOrSource::Variable(condition_result),
            false_jump_to: break_label,
        });
        Ok(())
    }
}

#[derive(Debug)]
pub enum LoopParameters {
    Until(NodeId),
    While(NodeId),
    For {
        var_name: Symbol,
        initial_value: Option<NodeId>,
        stop_value: NodeId,
        step: Option<NodeId>,
        ascending: bool,
        inclusive: bool,
    },
}

#[derive(Clone, Debug)]
pub struct Break {
    pub name: Option<Symbol>,
    pub value: Option<NodeId>,
}

impl Break {
    fn generate_code(
        &self,
        _result: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        if let Some(loop_info) = operations.loop_info(self.name.as_ref()) {
            let break_label = loop_info.break_label;
            if let Some(value) = self.value {
                let result = loop_info.loop_result;
                let value = tree.node(value);
                value.generate_code(result, operations, tree)?;
            }
            operations.push(Instruction::JumpTo(break_label));
            Ok(())
        } else {
            todo!("not in a loop or invalid loop name")
        }
    }
}

#[derive(Clone, Debug)]
pub struct Continue {
    pub name: Option<Symbol>,
}

impl Continue {
    fn generate_code(
        &self,
        _result: Destination,
        operations: &mut CodeBlockBuilder,
        _tree: &ExpressionTree,
    ) -> Result<(), CompilationError> {
        if let Some(loop_info) = operations.loop_info(self.name.as_ref()) {
            let continue_label = loop_info.continue_label;
            operations.push(Instruction::JumpTo(continue_label));
            Ok(())
        } else {
            todo!("not in a loop or invalid loop name")
        }
    }
}

#[derive(Debug, Default)]
pub struct SyntaxTreeBuilder(RefCell<Vec<Node>>);

impl SyntaxTreeBuilder {
    #[must_use]
    pub const fn new() -> Self {
        Self(RefCell::new(Vec::new()))
    }

    fn push(&self, node: Node) -> NodeId {
        let mut nodes = self.0.borrow_mut();
        let id = NodeId(nodes.len());
        nodes.push(node);
        id
    }

    pub fn if_node(&self, node: If) -> NodeId {
        self.push(Node::If(node))
    }

    pub fn loop_node(&self, node: Loop) -> NodeId {
        self.push(Node::Loop(node))
    }

    pub fn break_node(&self, node: Break) -> NodeId {
        self.push(Node::Break(node))
    }

    pub fn continue_node(&self, node: Continue) -> NodeId {
        self.push(Node::Continue(node))
    }

    pub fn binop_node(&self, kind: BinOpKind, left: NodeId, right: NodeId) -> NodeId {
        self.push(Node::BinOp(BinOp { kind, left, right }))
    }

    pub fn compare_node(&self, comparison: Comparison, left: NodeId, right: NodeId) -> NodeId {
        self.binop_node(BinOpKind::Compare(comparison), left, right)
    }

    pub fn assign_node(&self, target: NodeId, value: NodeId) -> NodeId {
        self.push(Node::Assign(Assign { target, value }))
    }

    pub fn statements<Nodes: IntoIterator<Item = NodeId>>(&self, nodes: Nodes) -> NodeId {
        self.push(Node::Block(Block(nodes.into_iter().collect())))
    }

    pub fn identifier(&self, identifier: impl Into<Symbol>) -> NodeId {
        self.push(Node::Identifier(identifier.into()))
    }

    pub fn integer(&self, integer: i64) -> NodeId {
        self.push(Node::Literal(Literal::Integer(integer)))
    }

    pub fn string(&self, string: String) -> NodeId {
        self.push(Node::Literal(Literal::String(string)))
    }

    pub fn real(&self, real: f64) -> NodeId {
        self.push(Node::Literal(Literal::Real(real)))
    }

    pub fn boolean(&self, boolean: bool) -> NodeId {
        self.push(Node::Literal(Literal::Boolean(boolean)))
    }

    pub fn not_node(&self, expr: NodeId) -> NodeId {
        self.push(Node::Not(Not { expr }))
    }

    pub fn call(&self, call: Call) -> NodeId {
        self.push(Node::Call(call))
    }

    pub fn return_node(&self, value: NodeId) -> NodeId {
        self.push(Node::Return(value))
    }

    pub fn map_node(&self, mappings: Vec<Mapping>) -> NodeId {
        self.push(Node::Map(Map { mappings }))
    }

    pub fn list_node(&self, values: Vec<NodeId>) -> NodeId {
        self.push(Node::List(List { values }))
    }

    pub fn finish(self, root: NodeId) -> ExpressionTree {
        ExpressionTree {
            nodes: self.0.into_inner(),
            root,
        }
    }
}

#[derive(Default, Debug)]
#[must_use]
pub struct CodeUnit {
    declarations_by_symbol: HashMap<Symbol, usize>,
    declarations: Vec<DeclaredSymbol>,
    vtable: Vec<Function>,
    modules: Vec<CodeUnit>,
    init_statements: Vec<NodeId>,
    init_tree: SyntaxTreeBuilder,
}

impl CodeUnit {
    pub fn from_tree(init_statements: Vec<NodeId>, init_tree: SyntaxTreeBuilder) -> Self {
        Self {
            declarations_by_symbol: HashMap::new(),
            declarations: Vec::new(),
            modules: Vec::new(),
            vtable: Vec::new(),
            init_statements,
            init_tree,
        }
    }

    pub fn new(init: impl FnOnce(&mut SyntaxTreeBuilder) -> Vec<NodeId>) -> Self {
        let mut init_tree = SyntaxTreeBuilder::default();
        let init_statements = init(&mut init_tree);
        Self::from_tree(init_statements, init_tree)
    }

    pub fn with(mut self, name: impl Into<Symbol>, declaration: impl Into<Declaration>) -> Self {
        let declaration_index = self.declarations.len();
        let declaration = match declaration.into() {
            Declaration::Function(function) => {
                let vtable_index = self.vtable.len();
                self.vtable.push(function);
                self.declarations_by_symbol
                    .insert(name.into(), declaration_index);
                DeclaredSymbol::Function(vtable_index)
            }
            Declaration::Module(module) => {
                let module_index = self.modules.len();
                self.modules.push(module);
                self.declarations_by_symbol
                    .insert(name.into(), declaration_index);
                DeclaredSymbol::Module(module_index)
            }
        };
        self.declarations.push(declaration);
        self
    }

    pub fn compile<InitScope: Scope>(
        self,
        scope: &mut InitScope,
    ) -> Result<Module, CompilationError> {
        let init = match self.init_statements.len() {
            0 => None,
            1 => Some(self.init_statements[0]),
            _ => Some(self.init_tree.statements(self.init_statements)),
        };
        let vtable = self
            .vtable
            .into_iter()
            .map(|f| {
                let mut block = CodeBlockBuilder::default();
                for (index, arg) in f.args.iter().enumerate() {
                    block.add_symbol(arg.clone(), ScopeSymbol::Argument(index));
                }
                f.body.generate_code(&mut block)?;
                Ok(ir::Function::new(f.name, f.args, block.finish()))
            })
            .collect::<Result<_, CompilationError>>()?;

        let init = if let Some(body) = init {
            let mut block = CodeBlockBuilder::default();
            // Define any existing variables
            scope.map_each_symbol(&mut |symbol, kind| match kind {
                ScopeSymbolKind::Variable => {
                    block.variable_index_from_name(&symbol);
                }
                ScopeSymbolKind::Function | ScopeSymbolKind::Argument => {}
            });
            self.init_tree.finish(body).generate_code(&mut block)?;
            for (symbol, variable) in block.variables() {
                scope.define_persistent_variable(symbol.clone(), *variable);
            }

            Some(ir::Function::new("__init", Vec::new(), block.finish()))
        } else {
            None
        };

        Ok(Module::new(
            vtable,
            self.modules
                .into_iter()
                .map(|unit| unit.compile(scope))
                .collect::<Result<_, CompilationError>>()?,
            init,
        ))
    }
}

#[derive(Debug)]
pub enum Declaration {
    Function(Function),
    Module(CodeUnit),
}

impl From<Function> for Declaration {
    fn from(function: Function) -> Self {
        Self::Function(function)
    }
}

impl From<CodeUnit> for Declaration {
    fn from(module: CodeUnit) -> Self {
        Self::Module(module)
    }
}

#[derive(Debug)]
enum DeclaredSymbol {
    Function(usize),
    Module(usize),
}

#[derive(Debug)]
pub struct Function {
    name: Option<Symbol>,
    args: Vec<Symbol>,
    body: ExpressionTree,
}

impl Function {
    pub fn new(name: impl OptionalSymbol, args: Vec<Symbol>, body: ExpressionTree) -> Self {
        Self {
            name: name.into_symbol(),
            args,
            body,
        }
    }

    #[must_use]
    pub fn name(&self) -> Option<&Symbol> {
        self.name.as_ref()
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum CompilationError {
    UndefinedFunction(Symbol),
    UndefinedIdentifier(Symbol),
    InvalidScope,
}

impl From<LinkError> for CompilationError {
    fn from(err: LinkError) -> Self {
        match err {
            LinkError::UndefinedFunction(name) => CompilationError::UndefinedFunction(name),
            LinkError::UndefinedIdentifier(name) => CompilationError::UndefinedIdentifier(name),
            LinkError::InvalidScopeOperation => CompilationError::InvalidScope,
            LinkError::InvalidLabel(_label) => unreachable!("invalid label encountered"),
        }
    }
}

impl std::error::Error for CompilationError {}

impl Display for CompilationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompilationError::UndefinedFunction(symbol) => {
                write!(f, "undefined function: {symbol}")
            }
            CompilationError::InvalidScope => {
                write!(f, "the scope used did not support a required operation")
            }
            CompilationError::UndefinedIdentifier(symbol) => {
                write!(f, "undefined identifier: {symbol}")
            }
        }
    }
}
