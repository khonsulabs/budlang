#![allow(missing_docs, clippy::missing_panics_doc)] // TODO docs and panics for ast

use std::{
    borrow::Cow,
    cell::RefCell,
    collections::HashMap,
    fmt::{Debug, Display},
};

use crate::{
    symbol::Symbol,
    vm::{self, Bud, Comparison, Environment, FromStack, Instruction, Value},
    Error,
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
        self.root().generate_code(block, self);
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
            Node::Block(block) => {
                let mut list = f.debug_list();
                for statement in &block.0 {
                    list.entry(&self.node(*statement));
                }
                list.finish()
            }
            Node::Literal(literal) => literal.fmt(f),
            Node::Identifier(identifier) => Debug::fmt(identifier, f),
            Node::Call(call) => {
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
    // UnaryOp(UnaryOp),
    Block(Block),
    Literal(Value),
    Identifier(Symbol),
    Call(Call),
    Return(NodeId),
}

impl Node {
    pub fn generate_code(&self, operations: &mut CodeBlockBuilder, tree: &ExpressionTree) {
        match self {
            Node::If(if_expr) => if_expr.generate_code(operations, tree),
            Node::BinOp(bin_op) => bin_op.generate_code(operations, tree),
            Node::Block(statements) => {
                let mut is_first = false;
                for statement in &statements.0 {
                    if is_first {
                        is_first = false;
                    } else {
                        // The last statement leaves a value behind.
                        operations.push(IntermediateOp::Pop);
                    }
                    let statement = tree.node(*statement);
                    statement.generate_code(operations, tree);
                }
            }
            Node::Literal(literal) => operations.push(IntermediateOp::Push(literal.clone())),
            Node::Identifier(identifier) => operations.push_from_symbol(identifier),
            Node::Call(call) => call.generate_code(operations, tree),
            Node::Return(value) => Self::generate_return(*value, operations, tree),
        }
    }

    fn generate_return(
        value_to_return: NodeId,
        operations: &mut CodeBlockBuilder,
        tree: &ExpressionTree,
    ) {
        let value_to_return = tree.node(value_to_return);
        value_to_return.generate_code(operations, tree);
        operations.push(IntermediateOp::Return);
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

    fn generate_code(&self, operations: &mut CodeBlockBuilder, tree: &ExpressionTree) {
        let condition = tree.node(self.condition);
        condition.generate_code(operations, tree);
        let if_false_label = self.else_block.map(|_| operations.new_label());
        let after_false_label = operations.new_label();
        operations.push(IntermediateOp::If {
            false_jump_to: if_false_label.unwrap_or(after_false_label),
        });
        let true_block = tree.node(self.true_block);
        true_block.generate_code(operations, tree);
        if let (Some(else_block), Some(if_false_label)) = (self.else_block, if_false_label) {
            operations.push(IntermediateOp::JumpTo(after_false_label));
            operations.label(if_false_label);
            let else_block = tree.node(else_block);
            else_block.generate_code(operations, tree);
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
    fn generate_code(&self, operations: &mut CodeBlockBuilder, tree: &ExpressionTree) {
        // Push right, left, then op
        let right = tree.node(self.right);
        right.generate_code(operations, tree);
        let left = tree.node(self.left);
        left.generate_code(operations, tree);
        self.kind.generate_code(operations);
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
    fn generate_code(&self, operations: &mut CodeBlockBuilder) {
        match self {
            BinOpKind::Add => operations.push(IntermediateOp::Add),
            BinOpKind::Sub => operations.push(IntermediateOp::Sub),
            BinOpKind::Multiply => operations.push(IntermediateOp::Multiply),
            BinOpKind::Divide => operations.push(IntermediateOp::Divide),
            BinOpKind::Compare(comparison) => operations.push(IntermediateOp::Compare(*comparison)),
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

    fn generate_code(&self, operations: &mut CodeBlockBuilder, tree: &ExpressionTree) {
        for &arg in &self.args {
            let arg = tree.node(arg);
            arg.generate_code(operations, tree);
        }

        match (self.target, self.name.as_ref()) {
            (None, None) => {
                // Recursive call
                operations.push(IntermediateOp::Call {
                    function: None,
                    arg_count: self.args.len(),
                });
            }
            (None, Some(symbol)) => {
                // Global call
                match operations.scope.get(symbol) {
                    Some(ScopeSymbol::Argument(_)) => {
                        todo!("calling a lambda function in an argument")
                    }
                    Some(ScopeSymbol::Function { function }) => {
                        operations.push(IntermediateOp::Call {
                            function: Some(function.clone()), // Switch to a Module/Index vtable lookup? We can't compile the code because of recursion.
                            arg_count: self.args.len(),
                        });
                    }
                    None => operations.push(IntermediateOp::Call {
                        function: Some(symbol.clone()), // Switch to a Module/Index vtable lookup? We can't compile the code because of recursion.
                        arg_count: self.args.len(),
                    }),
                }
            }
            _ => todo!("message"),
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

    pub fn statements<Nodes: IntoIterator<Item = NodeId>>(&self, nodes: Nodes) -> NodeId {
        self.push(Node::Block(Block(nodes.into_iter().collect())))
    }

    pub fn identifier(&self, identifier: impl Into<Symbol>) -> NodeId {
        self.push(Node::Identifier(identifier.into()))
    }

    pub fn integer(&self, integer: i64) -> NodeId {
        self.push(Node::Literal(Value::Integer(integer)))
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

#[derive(Default)]
pub struct CodeBlockBuilder {
    labels: Vec<Option<usize>>,
    ops: Vec<IntermediateOp>,
    args: usize,
    scope: HashMap<Symbol, ScopeSymbol>,
}

impl CodeBlockBuilder {
    pub fn add_symbol(&mut self, symbol: impl Into<Symbol>, value: ScopeSymbol) {
        if matches!(&value, ScopeSymbol::Argument(_)) {
            self.args += 1;
        }

        self.scope.insert(symbol.into(), value);
    }

    pub fn new_label(&mut self) -> Label {
        let label_id = self.labels.len();
        self.labels.push(None);
        Label(label_id)
    }

    pub fn push(&mut self, operation: IntermediateOp) {
        self.ops.push(operation);
    }

    pub fn label(&mut self, label: Label) {
        self.labels[label.0] = Some(self.ops.len());
    }

    pub fn push_from_symbol(&mut self, symbol: &Symbol) {
        match self.scope.get(symbol).unwrap() {
            ScopeSymbol::Argument(index) => {
                self.ops.push(IntermediateOp::PushCopy(*index));
            }
            ScopeSymbol::Function { .. } => todo!("pushing a vtable entry?"),
        }
    }

    pub fn finish<Env>(self, scope: &Bud<Env>) -> Result<Vec<Instruction>, CompilationError>
    where
        Env: Environment,
    {
        self.ops
            .into_iter()
            .map(|op| {
                Ok(match op {
                    IntermediateOp::Add => Instruction::Add,
                    IntermediateOp::Sub => Instruction::Sub,
                    IntermediateOp::Multiply => Instruction::Multiply,
                    IntermediateOp::Divide => Instruction::Divide,
                    IntermediateOp::If { false_jump_to } => Instruction::If {
                        false_jump_to: self.labels[false_jump_to.0].expect("label not inserted"),
                    },
                    IntermediateOp::JumpTo(label) => {
                        Instruction::JumpTo(self.labels[label.0].expect("label not inserted"))
                    }
                    IntermediateOp::Compare(comparison) => Instruction::Compare(comparison),
                    IntermediateOp::Push(value) => Instruction::Push(value),
                    IntermediateOp::PushVariable(variable) => Instruction::PushVariable(variable.0),
                    IntermediateOp::PushCopy(arg) => Instruction::PushArg(arg),
                    IntermediateOp::Pop => Instruction::PopAndDrop,
                    IntermediateOp::Return => Instruction::Return,
                    IntermediateOp::PopToVariable(variable_index) => {
                        Instruction::PopToVariable(variable_index.0)
                    }
                    IntermediateOp::Call {
                        function,
                        arg_count,
                    } => {
                        let vtable_index = function
                            .map(|symbol| {
                                scope
                                    .resolve_function_vtable_index(&symbol)
                                    .ok_or(CompilationError::UndefinedFunction(symbol))
                            })
                            .transpose()?;
                        Instruction::Call {
                            vtable_index,
                            arg_count,
                        }
                    }
                })
            })
            .collect::<Result<_, CompilationError>>()
    }
}

#[derive(Debug)]
pub enum ScopeSymbol {
    Argument(usize),
    Function { function: Symbol },
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
        let init =
            init.map(|body| Function::new("__init", Vec::new(), self.init_tree.finish(body)));
        UnlinkedCodeUnit {
            vtable: self.vtable,
            modules: self.modules.into_iter().map(CodeUnit::compile).collect(),
            init,
        }
    }
}

#[derive(Debug)]
pub struct UnlinkedCodeUnit {
    vtable: Vec<Function>,
    modules: Vec<UnlinkedCodeUnit>,
    init: Option<Function>,
}

impl UnlinkedCodeUnit {
    /// Runs all code in this unit in the passed context.
    pub fn execute_in<'a, Output: FromStack, Env>(
        &self,
        context: &'a mut Bud<Env>,
    ) -> Result<Output, Error<'a, Env, Output>>
    where
        Env: Environment,
    {
        // Process all modules first
        for _module in &self.modules {
            todo!()
        }

        // Compile each function
        for function in &self.vtable {
            function.compile_into(context)?;
        }

        // Execute the module initializer if it exists
        if let Some(init) = &self.init {
            let vtable_index = init.compile_into(context)?;
            context
                .run(Cow::Owned(vec![Instruction::Call {
                    vtable_index: Some(vtable_index),
                    arg_count: 0,
                }]))
                .map_err(Error::from)
        } else {
            Output::from_stack(context).map_err(Error::from)
        }
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

    pub fn compile_into<Env>(&self, context: &mut Bud<Env>) -> Result<usize, CompilationError>
    where
        Env: Environment,
    {
        let name = self
            .name
            .clone()
            .expect("compiling an unnamed function into a context isn't allowed");
        let mut block = CodeBlockBuilder::default();
        for (index, arg) in self.args.iter().enumerate() {
            block.add_symbol(arg.clone(), ScopeSymbol::Argument(index));
        }
        self.body.generate_code(&mut block);
        let ops = block.finish(context)?;
        let function = vm::Function {
            arg_count: self.args.len(),
            code: ops,
            variable_count: 0,
        };
        let vtable_index = context.define_function(name, function);
        Ok(vtable_index)
    }

    #[must_use]
    pub fn name(&self) -> Option<&Symbol> {
        self.name.as_ref()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Label(usize);

#[derive(Debug, Clone, Copy)]
pub struct Variable(usize);

#[derive(Debug, Clone)]
pub enum IntermediateOp {
    Add,
    Sub,
    Multiply,
    Divide,
    If {
        false_jump_to: Label,
    },
    JumpTo(Label),
    Compare(Comparison),
    Push(Value),
    PushVariable(Variable),
    PushCopy(usize),
    Pop,
    Return,
    PopToVariable(Variable),
    Call {
        function: Option<Symbol>,
        arg_count: usize,
    },
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

pub trait OptionalSymbol {
    fn into_symbol(self) -> Option<Symbol>;
}

impl OptionalSymbol for Symbol {
    fn into_symbol(self) -> Option<Symbol> {
        Some(self)
    }
}

impl OptionalSymbol for Option<Symbol> {
    fn into_symbol(self) -> Option<Symbol> {
        self
    }
}

impl<'a> OptionalSymbol for &'a str {
    fn into_symbol(self) -> Option<Symbol> {
        Some(Symbol::from(self))
    }
}
