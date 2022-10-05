#![allow(missing_docs, clippy::missing_panics_doc)] // TODO docs and panics for ast

use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::{Debug, Display},
};

use crate::{
    ir::{
        self, CodeBlockBuilder, CompareAction, Destination, Instruction, ScopeSymbol,
        UnlinkedCodeUnit, ValueOrSource,
    },
    symbol::{OptionalSymbol, Symbol},
    vm::{Comparison, Value},
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

    pub fn generate_code(&self, block: &mut CodeBlockBuilder) {
        self.root().generate_code(Destination::Return, block, self);
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
                .field("left", &binop.left)
                .field("right", &binop.right)
                .finish(),
            Node::Assign(assign) => f
                .debug_struct("Assign")
                .field("target", &self.node(assign.target))
                .field("value", &self.node(assign.value))
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
        }
    }
}

#[derive(Debug)]
enum Node {
    If(If),
    BinOp(BinOp),
    Assign(Assign),
    // UnaryOp(UnaryOp),
    Block(Block),
    Literal(Value),
    Identifier(Symbol),
    // Lookup(Lookup),
    Call(Call),
    Return(NodeId),
}

impl Node {
    pub fn generate_code(
        &self,
        result: Destination,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) {
        match self {
            Node::If(if_expr) => if_expr.generate_code(result, operations, tree),
            Node::BinOp(bin_op) => bin_op.generate_code(result, operations, tree),
            Node::Block(statements) => {
                let mut last_result_var = None;
                for statement in &statements.0 {
                    let statement = tree.node(*statement);
                    let result = operations.new_temporary_variable();
                    statement.generate_code(Destination::Variable(result), operations, tree);
                    last_result_var = Some(result);
                }
                if let Some(last_result) = last_result_var {
                    operations.store_into_destination(ValueOrSource::Variable(last_result), result);
                }
            }
            Node::Assign(assign) => assign.generate_code(result, operations, tree),
            Node::Literal(literal) => {
                operations.store_into_destination(ValueOrSource::Value(literal.clone()), result);
            }
            Node::Identifier(identifier) => {
                operations.load_from_symbol(identifier, result);
            }
            // Node::Lookup(lookup) => lookup.generate_code(operations, tree),
            Node::Call(call) => call.generate_code(result, operations, tree),
            Node::Return(value) => {
                Self::generate_return(*value, operations, tree);
            }
        }
    }

    pub fn to_value_or_source(
        &self,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) -> ValueOrSource {
        match self {
            Node::Literal(literal) => ValueOrSource::Value(literal.clone()),
            Node::Identifier(identifier) => match operations.symbol(identifier) {
                Some(ScopeSymbol::Argument(arg)) => ValueOrSource::Argument(*arg),
                Some(ScopeSymbol::Variable(var)) => ValueOrSource::Variable(*var),
                _ => todo!("error: unexpected/unknown symbol"),
            },
            // Node::Lookup(lookup) => lookup.generate_code(operations, tree),
            // Node::Call(call) => call.generate_code(result, operations, tree),
            // Node::Return(value) => {
            //     Self::generate_return(*value, operations, tree);
            // }
            _ => {
                let variable = operations.new_temporary_variable();
                self.generate_code(Destination::Variable(variable), operations, tree);
                ValueOrSource::Variable(variable)
            }
        }
    }

    fn generate_return(
        value_to_return: NodeId,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) {
        let value_to_return = tree.node(value_to_return);
        value_to_return.generate_code(Destination::Return, operations, tree);
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
    ) {
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
            let left = tree.node(*left).to_value_or_source(operations, tree);
            let right = tree.node(*right).to_value_or_source(operations, tree);
            operations.push(Instruction::Compare {
                comparison: *comparison,
                left,
                right,
                action: CompareAction::JumpIfFalse(false_jump_to),
            });
        } else {
            // The if statement is a result of something more complex
            let condition_result = operations.new_temporary_variable();
            condition.generate_code(Destination::Variable(condition_result), operations, tree);
            operations.push(Instruction::If {
                condition: ValueOrSource::Variable(condition_result),
                false_jump_to,
            });
        }
        let true_block = tree.node(self.true_block);
        true_block.generate_code(result, operations, tree);
        if let (Some(else_block), Some(if_false_label)) = (self.else_block, if_false_label) {
            operations.push(Instruction::JumpTo(after_false_label));
            operations.label(if_false_label);
            let else_block = tree.node(else_block);
            else_block.generate_code(result, operations, tree);
        }
        operations.label(after_false_label);
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
    ) {
        self.kind
            .generate_code(self.left, self.right, result, operations, tree);
    }
}

#[derive(Debug)]
pub enum BinOpKind {
    Add,
    Sub,
    Multiply,
    Divide,
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
    ) {
        let left = tree.node(left);
        let right = tree.node(right);
        let left = left.to_value_or_source(operations, tree);
        let right = right.to_value_or_source(operations, tree);

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
            BinOpKind::Compare(comparison) => operations.push(Instruction::Compare {
                comparison: *comparison,
                left,
                right,
                action: CompareAction::Store(destination),
            }),
        }
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
    ) {
        match (self.target, self.name.as_ref()) {
            (None, None) => {
                // Recursive call
                for &arg in &self.args {
                    let arg = tree.node(arg);
                    arg.generate_code(Destination::Stack, operations, tree);
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
                    arg.generate_code(Destination::Stack, operations, tree);
                }

                match operations.lookup(symbol) {
                    Some(ScopeSymbol::Argument(_) | ScopeSymbol::Variable(_)) => {
                        todo!("calling a lambda function in an argument")
                    }
                    Some(ScopeSymbol::Function { function }) => {
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
                let target_result = operations.new_temporary_variable();
                target.generate_code(Destination::Variable(target_result), operations, tree);

                // Push the arguments
                for &arg in &self.args {
                    let arg = tree.node(arg);
                    arg.generate_code(Destination::Stack, operations, tree);
                }

                // Invoke the call
                operations.push(Instruction::CallInstance {
                    target: Some(ValueOrSource::Variable(target_result)),
                    name: name.clone(),
                    arg_count: self.args.len(),
                    destination,
                });
            }
            (Some(_), None) => todo!("invalid instruction"),
        }
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
    ) {
        match tree.node(self.target) {
            Node::Identifier(name) => {
                let variable = operations.variable_index_from_name(name);
                let value = tree.node(self.value);
                value.generate_code(Destination::Variable(variable), operations, tree);
                operations.store_into_destination(ValueOrSource::Variable(variable), result);
            }
            _ => todo!("not a variable name"),
        }
    }
}

// #[derive(Debug, Clone)]
// pub struct Lookup {
//     base: NodeId,
//     name: Symbol,
// }

// impl Lookup {
//     fn generate_code(&self, operations: &mut CodeBlockBuilder, tree: &ExpressionTree) {
//         todo!()
//     }
// }

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

    pub fn binop_node(&self, kind: BinOpKind, left: NodeId, right: NodeId) -> NodeId {
        self.push(Node::BinOp(BinOp { kind, left, right }))
    }

    pub fn compare_node(&self, comparison: Comparison, left: NodeId, right: NodeId) -> NodeId {
        self.push(Node::BinOp(BinOp {
            kind: BinOpKind::Compare(comparison),
            left,
            right,
        }))
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
        self.push(Node::Literal(Value::Integer(integer)))
    }

    pub fn real(&self, real: f64) -> NodeId {
        self.push(Node::Literal(Value::Real(real)))
    }

    pub fn call(&self, call: Call) -> NodeId {
        self.push(Node::Call(call))
    }

    pub fn return_node(&self, value: NodeId) -> NodeId {
        self.push(Node::Return(value))
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

    pub fn compile(self) -> UnlinkedCodeUnit {
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
                f.body.generate_code(&mut block);
                ir::Function::new(f.name, f.args, block.finish())
            })
            .collect();

        let init = init.map(|body| {
            let mut block = CodeBlockBuilder::default();
            self.init_tree.finish(body).generate_code(&mut block);
            ir::Function::new("__init", Vec::new(), block.finish())
        });
        UnlinkedCodeUnit::new(
            vtable,
            self.modules.into_iter().map(CodeUnit::compile).collect(),
            init,
        )
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

#[derive(Debug)]
pub enum CompilationError {
    UndefinedFunction(Symbol),
}

impl std::error::Error for CompilationError {}

impl Display for CompilationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompilationError::UndefinedFunction(symbol) => {
                write!(f, "undefined function: {symbol}")
            }
        }
    }
}
