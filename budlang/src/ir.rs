#![allow(missing_docs, clippy::missing_panics_doc)] // TODO docs and panics for ir

use std::{
    borrow::Cow,
    collections::HashMap,
    env,
    fmt::{Display, Write},
};

use crate::{
    ast::{CompilationError, NodeId},
    symbol::{OptionalSymbol, Symbol},
    vm::{
        self, Bud, Comparison, Environment, FromStack, Intrinsic, StringLiteralDisplay, Value,
        ValueOrSource,
    },
    Error,
};

#[derive(Debug, Clone, Copy)]
pub struct Label(pub(crate) usize);

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Variable(usize);

impl Variable {
    #[must_use]
    pub fn index(self) -> usize {
        self.0
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.0)
    }
}

pub enum DagNode {
    Add,
}

#[derive(Debug, Clone)]
pub enum Instruction {
    Add {
        left: LiteralOrSource,
        right: LiteralOrSource,
        destination: Destination,
    },
    Sub {
        left: LiteralOrSource,
        right: LiteralOrSource,
        destination: Destination,
    },
    Multiply {
        left: LiteralOrSource,
        right: LiteralOrSource,
        destination: Destination,
    },
    Divide {
        left: LiteralOrSource,
        right: LiteralOrSource,
        destination: Destination,
    },
    If {
        condition: LiteralOrSource,
        false_jump_to: Label,
    },
    JumpTo(Label),
    Label(Label),
    Compare {
        comparison: Comparison,
        left: LiteralOrSource,
        right: LiteralOrSource,
        action: CompareAction,
    },
    Push(LiteralOrSource),
    PopAndDrop,
    Load {
        value: LiteralOrSource,
        variable: Variable,
    },
    Return(Option<LiteralOrSource>),
    Call {
        function: Option<Symbol>,
        arg_count: usize,
        destination: Destination,
    },
    CallIntrinsic {
        intrinsic: Intrinsic,
        arg_count: usize,
        destination: Destination,
    },
    CallInstance {
        target: Option<LiteralOrSource>,
        name: Symbol,
        arg_count: usize,
        destination: Destination,
    },
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::Add {
                left,
                right,
                destination,
            } => write!(f, "add {left} {right} {destination}"),
            Instruction::Sub {
                left,
                right,
                destination,
            } => write!(f, "sub {left} {right} {destination}"),
            Instruction::Multiply {
                left,
                right,
                destination,
            } => write!(f, "mul {left} {right} {destination}"),
            Instruction::Divide {
                left,
                right,
                destination,
            } => write!(f, "div {left} {right} {destination}"),
            Instruction::If {
                condition,
                false_jump_to,
            } => write!(f, "if !{condition} jump {false_jump_to}"),
            Instruction::JumpTo(label) => write!(f, "jump {label}"),
            Instruction::Label(label) => write!(f, "label {label}"),
            Instruction::Compare {
                comparison,
                left,
                right,
                action,
            } => write!(f, "{comparison} {left} {right} {action}"),
            Instruction::Push(value) => write!(f, "push {value}"),
            Instruction::PopAndDrop => write!(f, "pop-and-drop"),
            Instruction::Load { value, variable } => write!(f, "load {value} {variable}"),
            Instruction::Return(opt_value) => {
                if let Some(value) = opt_value {
                    write!(f, "return {value}")
                } else {
                    f.write_str("return")
                }
            }
            Instruction::Call {
                function,
                arg_count,
                destination,
            } => {
                if let Some(function) = function {
                    write!(f, "call {function} {arg_count} {destination}")
                } else {
                    write!(f, "recurse-call {arg_count} {destination}")
                }
            }
            Instruction::CallIntrinsic {
                intrinsic,
                arg_count,
                destination,
            } => {
                write!(f, "intrinsic {intrinsic} {arg_count} {destination}")
            }
            Instruction::CallInstance {
                target,
                name,
                arg_count,
                destination,
            } => {
                if let Some(target) = target {
                    write!(f, "invoke {target} {name} {arg_count} {destination}")
                } else {
                    write!(f, "invoke stack {name} {arg_count} {destination}")
                }
            }
        }
    }
}

/// A literal value.
#[derive(Debug, Clone)]
pub enum Literal {
    /// A literal that represents [`Value::Void`].
    Void,
    /// A signed 64-bit integer literal value.
    Integer(i64),
    /// A real number literal value (64-bit floating point).
    Real(f64),
    /// A boolean literal.
    Boolean(bool),
    /// A string literal.
    String(String),
}

#[derive(Debug, Clone)]
pub struct Mapping {
    pub key: NodeId,
    pub value: NodeId,
}

impl Literal {
    #[must_use]
    pub fn instantiate<Env>(&self) -> Value
    where
        Env: Environment,
    {
        match self {
            Literal::Void => Value::Void,
            Literal::Integer(value) => Value::Integer(*value),
            Literal::Real(value) => Value::Real(*value),
            Literal::Boolean(value) => Value::Boolean(*value),
            Literal::String(value) => Value::dynamic(<Env::String as From<&str>>::from(value)),
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(value) => Display::fmt(value, f),
            Self::Real(value) => Display::fmt(value, f),
            Self::Boolean(value) => Display::fmt(value, f),
            Self::String(string) => Display::fmt(&StringLiteralDisplay::new(string), f),
            Self::Void => f.write_str("Void"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ValueSource {
    /// The value is in an argument at the provided 0-based index.
    Argument(usize),
    /// The value is in a variable specified.
    Variable(Variable),
}

impl Display for ValueSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueSource::Argument(index) => write!(f, "@{index}"),
            ValueSource::Variable(variable) => Display::fmt(variable, f),
        }
    }
}

impl<'a> From<&'a ValueSource> for vm::ValueSource {
    fn from(source: &'a ValueSource) -> Self {
        match source {
            ValueSource::Argument(arg) => Self::Argument(*arg),
            ValueSource::Variable(var) => Self::Variable(var.0),
        }
    }
}

#[derive(Debug, Clone)]
pub enum LiteralOrSource {
    Literal(Literal),
    /// The value is in an argument at the provided 0-based index.
    Argument(usize),
    /// The value is in a variable specified.
    Variable(Variable),
}

impl LiteralOrSource {
    #[must_use]
    pub fn instantiate<Env>(&self) -> ValueOrSource
    where
        Env: Environment,
    {
        match self {
            LiteralOrSource::Literal(literal) => ValueOrSource::Value(literal.instantiate::<Env>()),
            LiteralOrSource::Argument(index) => ValueOrSource::Argument(*index),
            LiteralOrSource::Variable(index) => ValueOrSource::Variable(index.0),
        }
    }
}

impl Display for LiteralOrSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LiteralOrSource::Literal(value) => Display::fmt(value, f),
            LiteralOrSource::Argument(index) => write!(f, "@{index}"),
            LiteralOrSource::Variable(variable) => Display::fmt(variable, f),
        }
    }
}

/// A destination for a value.
#[derive(Debug, Clone, Copy)]
pub enum Destination {
    /// Store the value in the 0-based variable index provided.
    Variable(Variable),
    /// Push the value to the stack.
    Stack,
    /// Store the value in the return register.
    Return,
}

impl Display for Destination {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Destination::Variable(variable) => Display::fmt(&variable, f),
            Destination::Stack => f.write_str("stack"),
            Destination::Return => f.write_str("$$"),
        }
    }
}

impl<'a> From<&'a Destination> for vm::Destination {
    fn from(source: &'a Destination) -> Self {
        match source {
            Destination::Variable(variable) => Self::Variable(variable.0),
            Destination::Stack => Self::Stack,
            Destination::Return => Self::Return,
        }
    }
}

/// An action to take during an [`Instruction::Compare`].
#[derive(Debug, Clone)]
pub enum CompareAction {
    /// Store the boolean result in the destination indicated.
    Store(Destination),
    /// If the comparison is false, jump to the 0-based instruction index
    /// indicated.
    JumpIfFalse(Label),
}

impl Display for CompareAction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompareAction::Store(destination) => Display::fmt(destination, f),
            CompareAction::JumpIfFalse(label) => write!(f, "jump {label}"),
        }
    }
}

impl CompareAction {
    #[must_use]
    pub fn link(&self, labels: &[Option<usize>]) -> vm::CompareAction {
        match self {
            CompareAction::Store(destination) => vm::CompareAction::Store(destination.into()),
            CompareAction::JumpIfFalse(target) => {
                vm::CompareAction::JumpIfFalse(labels.get(target.0).unwrap().unwrap())
            }
        }
    }
}

#[derive(Default)]
pub struct CodeBlockBuilder {
    label_counter: usize,
    ops: Vec<Instruction>,
    args: usize,
    temporary_variables: usize,
    scope: HashMap<Symbol, ScopeSymbol>,
    pub(crate) variables: HashMap<Symbol, Variable>,
}

impl CodeBlockBuilder {
    pub(crate) fn add_symbol(&mut self, symbol: impl Into<Symbol>, value: ScopeSymbol) {
        if matches!(&value, ScopeSymbol::Argument(_)) {
            self.args += 1;
        }

        self.scope.insert(symbol.into(), value);
    }

    pub fn new_label(&mut self) -> Label {
        let label_id = self.label_counter;
        self.label_counter += 1;
        Label(label_id)
    }

    pub fn push(&mut self, operation: Instruction) {
        self.ops.push(operation);
    }

    pub fn label(&mut self, label: Label) {
        self.push(Instruction::Label(label));
    }

    pub fn push_from_symbol(&mut self, symbol: &Symbol) {
        match self.scope.get(symbol).unwrap() {
            ScopeSymbol::Argument(index) => {
                self.ops
                    .push(Instruction::Push(LiteralOrSource::Argument(*index)));
            }
            ScopeSymbol::Variable(variable) => {
                self.ops
                    .push(Instruction::Push(LiteralOrSource::Variable(*variable)));
            }
            ScopeSymbol::Function { .. } => todo!("pushing a vtable entry?"),
        }
    }

    #[must_use]
    pub fn lookup(&self, symbol: &Symbol) -> Option<&ScopeSymbol> {
        self.scope.get(symbol)
    }

    pub fn store_into_destination(&mut self, value: LiteralOrSource, destination: Destination) {
        match destination {
            Destination::Variable(variable) => {
                self.push(Instruction::Load { value, variable });
            }
            Destination::Stack => {
                self.push(Instruction::Push(value));
            }
            Destination::Return => {
                self.push(Instruction::Return(Some(value)));
            }
        }
    }

    #[must_use]
    pub fn symbol(&self, symbol: &Symbol) -> Option<&ScopeSymbol> {
        self.scope.get(symbol)
    }

    pub fn load_from_symbol(
        &mut self,
        symbol: &Symbol,
        destination: Destination,
    ) -> Result<(), CompilationError> {
        match self.scope.get(symbol) {
            Some(ScopeSymbol::Argument(index)) => {
                self.store_into_destination(LiteralOrSource::Argument(*index), destination);
                Ok(())
            }
            Some(ScopeSymbol::Variable(variable)) => {
                self.store_into_destination(LiteralOrSource::Variable(*variable), destination);
                Ok(())
            }
            Some(ScopeSymbol::Function { .. }) => todo!("pushing a vtable entry?"),
            None => Err(CompilationError::UndefinedIdentifier(symbol.clone())),
        }
    }

    pub fn variable_index_from_name(&mut self, name: &Symbol) -> Variable {
        let new_index = self.variables.len();
        let variable = *self
            .variables
            .entry(name.clone())
            .or_insert_with(|| Variable(new_index));
        if variable.0 == new_index {
            self.add_symbol(name.clone(), ScopeSymbol::Variable(variable));
        }
        variable
    }

    pub fn new_temporary_variable(&mut self) -> Variable {
        self.temporary_variables += 1;
        let variable = self.variable_index_from_name(&Symbol::from(
            format!("${}", self.temporary_variables).as_str(),
        ));
        variable
    }

    #[must_use]
    pub fn finish(self) -> CodeBlock {
        CodeBlock {
            variables: self.variables.len(),
            code: self.ops,
        }
    }
}

#[derive(Debug)]
pub struct CodeBlock {
    pub variables: usize,
    pub code: Vec<Instruction>,
}

impl CodeBlock {
    #[allow(clippy::too_many_lines)]
    pub fn link<S>(&self, scope: &S) -> Result<vm::CodeBlock, CompilationError>
    where
        S: Scope,
    {
        let mut labels = Vec::new();
        let mut labels_encountered = 0;
        for (index, op) in self.code.iter().enumerate() {
            if let Instruction::Label(label) = op {
                if labels.len() <= label.0 {
                    labels.resize(label.0 + 1, None);
                }
                labels[label.0] = Some(index - labels_encountered);
                labels_encountered += 1;
            }
        }
        self.code
            .iter()
            .filter_map(|op| compile_instruction(op, &labels, scope).transpose())
            .collect::<Result<_, CompilationError>>()
            .map(|instructions| vm::CodeBlock {
                variables: self.variables,
                code: instructions,
            })
    }
}

impl Display for CodeBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut is_first = true;
        for i in &self.code {
            if is_first {
                is_first = false;
            } else {
                f.write_char('\n')?;
            }
            Display::fmt(i, f)?;
        }
        Ok(())
    }
}

#[allow(clippy::too_many_lines)] // Most are straight mappings...
fn compile_instruction<S>(
    op: &Instruction,
    labels: &[Option<usize>],
    scope: &S,
) -> Result<Option<vm::Instruction>, CompilationError>
where
    S: Scope,
{
    Ok(Some(match op {
        Instruction::Add {
            left,
            right,
            destination,
        } => vm::Instruction::Add {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::Sub {
            left,
            right,
            destination,
        } => vm::Instruction::Sub {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::Multiply {
            left,
            right,
            destination,
        } => vm::Instruction::Multiply {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::Divide {
            left,
            right,
            destination,
        } => vm::Instruction::Divide {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::If {
            condition,
            false_jump_to,
        } => vm::Instruction::If {
            condition: condition.instantiate::<S::Environment>(),
            false_jump_to: labels[false_jump_to.0].expect("label not inserted"),
        },
        Instruction::JumpTo(label) => {
            vm::Instruction::JumpTo(labels[label.0].expect("label not inserted"))
        }
        Instruction::Label(_label) => return Ok(None), // Labels are no-ops
        Instruction::Compare {
            comparison,
            left,
            right,
            action,
        } => vm::Instruction::Compare {
            comparison: *comparison,
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            action: action.link(labels),
        },
        Instruction::Push(value) => vm::Instruction::Push(value.instantiate::<S::Environment>()),
        Instruction::PopAndDrop => vm::Instruction::PopAndDrop,
        Instruction::Return(value) => vm::Instruction::Return(
            value
                .as_ref()
                .map(LiteralOrSource::instantiate::<S::Environment>),
        ),
        Instruction::Load { value, variable } => vm::Instruction::Load {
            variable_index: variable.0,
            value: value.instantiate::<S::Environment>(),
        },
        Instruction::Call {
            function,
            arg_count,
            destination,
        } => {
            let vtable_index = function
                .as_ref()
                .map(|symbol| {
                    scope
                        .resolve_function_vtable_index(symbol)
                        .ok_or_else(|| CompilationError::UndefinedFunction(symbol.clone()))
                })
                .transpose()?;
            vm::Instruction::Call {
                vtable_index,
                arg_count: *arg_count,
                destination: destination.into(),
            }
        }
        Instruction::CallInstance {
            target,
            name,
            arg_count,
            destination,
        } => vm::Instruction::CallInstance {
            target: target
                .as_ref()
                .map(LiteralOrSource::instantiate::<S::Environment>),
            name: name.clone(),
            arg_count: *arg_count,
            destination: destination.into(),
        },
        Instruction::CallIntrinsic {
            intrinsic,
            arg_count,
            destination,
        } => vm::Instruction::CallIntrinsic {
            intrinsic: *intrinsic,
            arg_count: *arg_count,
            destination: destination.into(),
        },
    }))
}

#[derive(Debug)]
pub enum ScopeSymbolKind {
    Argument,
    Variable,
    Function,
}

#[derive(Debug)]
pub enum ScopeSymbol {
    Argument(usize),
    Variable(Variable),
    Function { function: Symbol },
}

#[derive(Debug)]
pub struct Function {
    pub name: Option<Symbol>,
    pub args: Vec<Symbol>,
    pub body: CodeBlock,
}

impl Function {
    pub fn new(name: impl OptionalSymbol, args: Vec<Symbol>, body: CodeBlock) -> Self {
        Self {
            name: name.into_symbol(),
            args,
            body,
        }
    }

    pub fn compile<S>(&self, context: &mut S) -> Result<vm::Function, CompilationError>
    where
        S: Scope,
    {
        let name = self
            .name
            .clone()
            .expect("compiling an unnamed function into a context isn't allowed");
        let block = self.body.link(context)?;
        if env::var("PRINT_IR").is_ok() {
            println!("{}", block.display_indented("  "));
        }
        let function = vm::Function {
            name,
            arg_count: self.args.len(),
            code: block.code,
            variable_count: block.variables,
        };
        Ok(function)
    }

    pub fn compile_into<S>(&self, context: &mut S) -> Result<usize, CompilationError>
    where
        S: Scope,
    {
        let function = self.compile(context)?;

        let vtable_index = context
            .define_function(function)
            .ok_or(CompilationError::InvalidScope)?;
        Ok(vtable_index)
    }

    #[must_use]
    pub fn name(&self) -> Option<&Symbol> {
        self.name.as_ref()
    }
}

#[derive(Debug)]
pub struct UnlinkedCodeUnit {
    pub vtable: Vec<Function>,
    pub modules: Vec<UnlinkedCodeUnit>,
    pub init: Option<Function>,
}

impl UnlinkedCodeUnit {
    #[must_use]
    pub fn new(
        vtable: Vec<Function>,
        modules: Vec<UnlinkedCodeUnit>,
        init: Option<Function>,
    ) -> Self {
        Self {
            vtable,
            modules,
            init,
        }
    }

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
        for (index, function) in self.vtable.iter().enumerate() {
            if env::var("PRINT_IR").is_ok() {
                if let Some(name) = &function.name {
                    println!(
                        "function #{index} - {name}({})",
                        function
                            .args
                            .iter()
                            .map(Symbol::as_str)
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                } else {
                    println!(
                        "function #{index}({})",
                        function
                            .args
                            .iter()
                            .map(Symbol::as_str)
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                }
            }
            function.compile_into(context)?;
        }

        // Execute the module initializer if it exists
        if let Some(init) = &self.init {
            if env::var("PRINT_IR").is_ok() {
                println!("function init");
            }
            let vtable_index = init.compile_into(context)?;
            context
                .run(
                    Cow::Owned(vec![vm::Instruction::Call {
                        vtable_index: Some(vtable_index),
                        arg_count: 0,
                        destination: vm::Destination::Stack,
                    }]),
                    0,
                )
                .map_err(Error::from)
        } else {
            Output::from_value(Value::Void).map_err(Error::from)
        }
    }
}

pub trait Scope {
    type Environment: Environment;

    /// Returns the vtable index of a function with the provided name.
    fn resolve_function_vtable_index(&self, name: &Symbol) -> Option<usize>;
    fn map_each_symbol(&self, callback: &mut impl FnMut(Symbol, ScopeSymbolKind));

    /// Defines a function with the provided name.
    fn define_function(&mut self, function: vm::Function) -> Option<usize>;
    fn define_variable(&mut self, name: Symbol, variable: Variable);
}

impl Scope for () {
    type Environment = ();

    fn resolve_function_vtable_index(&self, _name: &Symbol) -> Option<usize> {
        None
    }

    fn map_each_symbol(&self, _callback: &mut impl FnMut(Symbol, ScopeSymbolKind)) {}

    fn define_function(&mut self, _function: vm::Function) -> Option<usize> {
        None
    }

    fn define_variable(&mut self, _name: Symbol, _variable: Variable) {}
}

// #[test]
// fn optimizations() {
//     let unit = crate::parser::parse(
//         r#"function fibonacci(n)
//             if n <= 2
//                 1
//             else
//                 this(n - 1) + this(n - 2)
//             end
//         end
//         "#,
//     )
//     .unwrap()
//     .compile();
//     println!("Unoptimized code:\n{}", unit.vtable[0].body);
//     println!("Unoptimized length: {}", unit.vtable[0].body.code.len());
//     let mut graph = crate::optimizer::CodeGraph::new(&unit.vtable[0].body.code);
//     println!("Graph:\n {graph}");
//     let dag = graph.dags();
//     println!("Dag:\n {dag:?}");
//     // dag.optimize(&mut graph);
// }
