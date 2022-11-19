//! An intermediate representation of virtual machine instructions.
//!
//! This intermediate representation provides conveniences for handling
//! variables, labels, and function calls.
use std::{
    borrow::{Borrow, BorrowMut, Cow},
    collections::HashMap,
    env,
    fmt::{Display, Write},
    ops::{Deref, DerefMut},
};

use crate::{
    symbol::{OptionalSymbol, Symbol},
    Comparison, Environment, Error, FromStack, Intrinsic, StringLiteralDisplay, Value,
    ValueOrSource, VirtualMachine,
};

/// A label that can be jumped to.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Label(pub(crate) usize);

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)
    }
}

/// A reference to a local variable.
#[derive(Debug, Clone, Copy)]
pub struct Variable(usize);

impl Variable {
    /// Returns the index of this variable on the stack.
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

/// An intermediate representation of an [`crate::Instruction`].
#[derive(Debug, Clone)]
pub enum Instruction {
    /// Adds `left` and `right` and places the result in `destination`.
    ///
    /// If this operation causes an overflow, [`Value::Void`] will be stored in
    /// the destination instead.
    Add {
        /// The left hand side of the operation.
        left: LiteralOrSource,
        /// The right hand side of the operation.
        right: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Subtracts `right` from `left` and places the result in `destination`.
    ///
    /// If this operation causes an overflow, [`Value::Void`] will be stored in
    /// the destination instead.
    Sub {
        /// The left hand side of the operation.
        left: LiteralOrSource,
        /// The right hand side of the operation.
        right: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Multiply `left` by `right` and places the result in `destination`.
    ///
    /// If this operation causes an overflow, [`Value::Void`] will be stored in
    /// the destination instead.
    Multiply {
        /// The left hand side of the operation.
        left: LiteralOrSource,
        /// The right hand side of the operation.
        right: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Divides `left` by `right` and places the result in `destination`.
    ///
    /// If this operation causes an overflow, [`Value::Void`] will be stored in
    /// the destination instead.
    Divide {
        /// The left hand side of the operation.
        left: LiteralOrSource,
        /// The right hand side of the operation.
        right: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Performs a logical and of `left` and `right` and places the result in
    /// `destination`. This operation always results in a [`Value::Boolean`].
    ///
    /// `left` and `right` will be checked for thruthyness. If both are truthy,
    /// this operation will store true in `destination`. Otherwise, false will
    /// be stored.
    ///
    /// # Short Circuiting
    ///
    /// This instruction will not evaluate `right`'s truthiness if `left` is
    /// false.
    LogicalAnd {
        /// The left hand side of the operation.
        left: LiteralOrSource,
        /// The right hand side of the operation.
        right: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Performs a logical or of `left` and `right` and places the result in
    /// `destination`. This operation always results in a [`Value::Boolean`].
    ///
    /// `left` and `right` will be checked for thruthyness. If either are
    /// truthy, this operation will store true in `destination`. Otherwise,
    /// false will be stored.
    ///
    /// # Short Circuiting
    ///
    /// This instruction will not evaluate `right`'s truthiness if `left` is
    /// true.
    LogicalOr {
        /// The left hand side of the operation.
        left: LiteralOrSource,
        /// The right hand side of the operation.
        right: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Performs a logical exclusive-or of `left` and `right` and places the result in
    /// `destination`. This operation always results in a [`Value::Boolean`].
    ///
    /// `left` and `right` will be checked for thruthyness. If one is truthy and
    /// the other is not, this operation will store true in `destination`.
    /// Otherwise, false will be stored.
    LogicalXor {
        /// The left hand side of the operation.
        left: LiteralOrSource,
        /// The right hand side of the operation.
        right: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Performs a bitwise and of `left` and `right` and places the result in
    /// `destination`. This operation always results in a [`Value::Integer`].
    ///
    /// If either `left` or `right ` are not [`Value::Integer`], a fault will be
    /// returned.
    ///
    /// The result will have each bit set based on whether the corresponding bit
    /// in both `left` and `right` are both 1.
    BitwiseAnd {
        /// The left hand side of the operation.
        left: LiteralOrSource,
        /// The right hand side of the operation.
        right: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Performs a bitwise or of `left` and `right` and places the result in
    /// `destination`. This operation always results in a [`Value::Integer`].
    ///
    /// If either `left` or `right ` are not [`Value::Integer`], a fault will be
    /// returned.
    ///
    /// The result will have each bit set based on whether either corresponding bit
    /// in `left` or `right` are 1.
    BitwiseOr {
        /// The left hand side of the operation.
        left: LiteralOrSource,
        /// The right hand side of the operation.
        right: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Performs a bitwise exclusive-or of `left` and `right` and places the
    /// result in `destination`. This operation always results in a
    /// [`Value::Integer`].
    ///
    /// If either `left` or `right ` are not [`Value::Integer`], a fault will be
    /// returned.
    ///
    /// The result will have each bit set based on whether only one
    /// corresponding bit in either `left` or `right` are 1.
    BitwiseXor {
        /// The left hand side of the operation.
        left: LiteralOrSource,
        /// The right hand side of the operation.
        right: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Performs a bitwise shift left of `left` by `right` bits, storing
    /// the result in `destination`.
    ///
    /// This operation requires both operands to be integers. If either are not
    /// integers, a fault will be returned.
    ShiftLeft {
        /// The value to shift
        left: LiteralOrSource,
        /// The number of bits to shift by
        right: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Performs a bitwise shift right of `left` by `right` bits, storing the
    /// result in `destination`.
    ///
    /// This operation requires both operands to be integers. If either are not
    /// integers, a fault will be returned.
    ShiftRight {
        /// The value to shift
        left: LiteralOrSource,
        /// The number of bits to shift by
        right: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Performs a `not` operation for `value`, storing the result in
    /// `destination`.
    ///
    /// If the operands is an integer, this performs a bitwise operation.
    /// Dynamic types can also implement custom behaviors for this operation.
    ///
    /// If no other implementations are provided for the given types, the result
    /// will be a boolean evaluation of `not value.is_truthy()`.
    Not {
        /// The left hand side of the operation.
        value: LiteralOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Checks [`condition.is_truthy()`](Value::is_truthy), jumping to the
    /// target label if false.
    ///
    /// If truthy, the virtual machine continues executing the next instruction
    /// in sequence.
    ///
    /// If not truthy, the virtual machine jumps to label `false_jump_to`.
    If {
        /// The source of the condition.
        condition: LiteralOrSource,
        /// The label to jump to if the condition is falsey.
        false_jump_to: Label,
    },
    /// Jump execution to the address of the given label.
    JumpTo(Label),
    /// Labels the next instruction with the given [`Label`].
    Label(Label),
    /// Compares `left` and `right` using `comparison` to evaluate a boolean
    /// result.
    ///
    /// If [`CompareAction::Store`] is used, the boolean result will be stored
    /// in the provided destination.
    ///
    /// If [`CompareAction::JumpIfFalse`] is used and the result is false,
    /// execution will jump to the label specified. If the result is true, the
    /// next instruction will continue executing.
    Compare {
        /// The comparison to perform.
        comparison: Comparison,
        /// The left hand side of the operation.
        left: LiteralOrSource,
        /// The right hand side of the operation.
        right: LiteralOrSource,
        /// The action to take with the result of the comparison.
        action: CompareAction,
    },
    /// Pushes a value to the stack.
    Push(LiteralOrSource),
    /// Loads a `value` into a variable.
    Load {
        /// The index of the variable to store the value in.
        value: LiteralOrSource,
        /// The value or source of the value to store.
        variable: Variable,
    },
    /// Returns from the current stack frame.
    Return(Option<LiteralOrSource>),
    /// Calls a function.
    ///
    /// When calling a function, values on the stack are "passed" to the
    /// function being pushed to the stack before calling the function. To
    /// ensure the correct number of arguments are taken even when variable
    /// argument lists are supported, the number of arguments is passed and
    /// controls the baseline of the stack.
    ///  
    /// Upon returning from a function call, the arguments will no longer be on
    /// the stack. The value returned from the function (or [`Value::Void`] if
    /// no value was returned) will be placed in `destination`.
    Call {
        /// The name of the function to call. If None, the current function is
        /// called recursively.
        function: Option<Symbol>,

        /// The number of arguments on the stack that should be used as
        /// arguments to this call.
        arg_count: usize,

        /// The destination for the result of the call.
        destination: Destination,
    },
    /// Calls an intrinsic runtime function.
    ///
    /// When calling a function, values on the stack are "passed" to the
    /// function being pushed to the stack before calling the function. To
    /// ensure the correct number of arguments are taken even when variable
    /// argument lists are supported, the number of arguments is passed and
    /// controls the baseline of the stack.
    ///  
    /// Upon returning from a function call, the arguments will no longer be on
    /// the stack. The value returned from the function (or [`Value::Void`] if
    /// no value was returned) will be placed in `destination`.
    CallIntrinsic {
        /// The runtime intrinsic to call.
        intrinsic: Intrinsic,
        /// The number of arguments on the stack that should be used as
        /// arguments to this call.
        arg_count: usize,
        /// The destination for the result of the call.
        destination: Destination,
    },
    /// Calls a function by name on a value.
    ///
    /// When calling a function, values on the stack are "passed" to the
    /// function being pushed to the stack before calling the function. To
    /// ensure the correct number of arguments are taken even when variable
    /// argument lists are supported, the number of arguments is passed and
    /// controls the baseline of the stack.
    ///  
    /// Upon returning from a function call, the arguments will no longer be on
    /// the stack. The value returned from the function (or [`Value::Void`] if
    /// no value was returned) will be placed in `destination`.
    CallInstance {
        /// The target of the function call. If None, the value on the stack
        /// prior to the arguments is the target of the call.
        target: Option<LiteralOrSource>,
        /// The name of the function to call.
        name: Symbol,
        /// The number of arguments on the stack that should be used as
        /// arguments to this call.
        arg_count: usize,
        /// The destination for the result of the call.
        destination: Destination,
    },
}

impl Display for Instruction {
    #[allow(clippy::too_many_lines)]
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
            Instruction::LogicalAnd {
                left,
                right,
                destination,
            } => write!(f, "and {left} {right} {destination}"),
            Instruction::LogicalOr {
                left,
                right,
                destination,
            } => write!(f, "or {left} {right} {destination}"),
            Instruction::LogicalXor {
                left,
                right,
                destination,
            } => write!(f, "xor {left} {right} {destination}"),
            Instruction::BitwiseAnd {
                left,
                right,
                destination,
            } => write!(f, "bitand {left} {right} {destination}"),
            Instruction::BitwiseOr {
                left,
                right,
                destination,
            } => write!(f, "bitor {left} {right} {destination}"),
            Instruction::BitwiseXor {
                left,
                right,
                destination,
            } => write!(f, "bitxor {left} {right} {destination}"),
            Instruction::ShiftLeft {
                left,
                right,
                destination,
            } => write!(f, "shl {left} {right} {destination}"),
            Instruction::ShiftRight {
                left,
                right,
                destination,
            } => write!(f, "shr {left} {right} {destination}"),
            Instruction::Not { value, destination } => write!(f, "not {value} {destination}"),
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

impl Literal {
    /// Create an instance of this literal in the given [`Environment`].
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

/// The source of a value.
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

impl<'a> From<&'a ValueSource> for crate::ValueSource {
    fn from(source: &'a ValueSource) -> Self {
        match source {
            ValueSource::Argument(arg) => Self::Argument(*arg),
            ValueSource::Variable(var) => Self::Variable(var.0),
        }
    }
}

/// A literal value or a location of a value
#[derive(Debug, Clone)]
pub enum LiteralOrSource {
    /// A literal.
    Literal(Literal),
    /// The value is in an argument at the provided 0-based index.
    Argument(usize),
    /// The value is in a variable specified.
    Variable(Variable),
}

impl LiteralOrSource {
    /// Instantiates this into a [`ValueOrSource`], promoting [`Literal`]s to
    /// [`Value`]s.
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

impl<'a> From<&'a Destination> for crate::Destination {
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
    /// Converts this intermediate representation of a compare action to the
    /// virtual machines [`CompareAction`](crate::CompareAction).
    pub fn link(&self, labels: &[Option<usize>]) -> Result<crate::CompareAction, LinkError> {
        match self {
            CompareAction::Store(destination) => {
                Ok(crate::CompareAction::Store(destination.into()))
            }
            CompareAction::JumpIfFalse(target) => Ok(crate::CompareAction::JumpIfFalse(
                labels
                    .get(target.0)
                    .and_then(|label| *label)
                    .ok_or(LinkError::InvalidLabel(*target))?,
            )),
        }
    }
}

/// A type that helps build [`CodeBlock`]s.
#[derive(Default)]
pub struct CodeBlockBuilder {
    label_counter: usize,
    ops: Vec<Instruction>,
    args: usize,
    temporary_variables: usize,
    scope: HashMap<Symbol, ScopeSymbol>,
    labels: CodeLabels,
    variables: HashMap<Symbol, Variable>,
}

impl CodeBlockBuilder {
    /// Adds a new symbol to this code block.
    pub fn add_symbol(&mut self, symbol: impl Into<Symbol>, value: ScopeSymbol) {
        if matches!(&value, ScopeSymbol::Argument(_)) {
            self.args += 1;
        }

        self.scope.insert(symbol.into(), value);
    }

    /// Create a new label.
    pub fn new_label(&mut self) -> Label {
        let label_id = self.label_counter;
        self.label_counter += 1;
        Label(label_id)
    }

    /// Push an instruction.
    pub fn push(&mut self, operation: Instruction) {
        self.ops.push(operation);
    }

    /// Label the next instruction as `label`.
    pub fn label(&mut self, label: Label) {
        self.push(Instruction::Label(label));
    }

    /// Looks up a symbol.
    #[must_use]
    pub fn lookup(&self, symbol: &Symbol) -> Option<&ScopeSymbol> {
        self.scope.get(symbol)
    }

    /// Returns the loop information for a given name, or the current loop if no
    /// name is provided.
    #[must_use]
    pub fn loop_info(&self, name: Option<&Symbol>) -> Option<&LoopInfo> {
        self.labels.find(name)
    }

    /// Adds the appropriate instruction to store `value` into `destination`.
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

    /// Adds the correct instruction to load a value from `symbol` and store it
    /// in `destination`.
    pub fn load_from_symbol(
        &mut self,
        symbol: &Symbol,
        destination: Destination,
    ) -> Result<(), LinkError> {
        match self.scope.get(symbol) {
            Some(ScopeSymbol::Argument(index)) => {
                self.store_into_destination(LiteralOrSource::Argument(*index), destination);
                Ok(())
            }
            Some(ScopeSymbol::Variable(variable)) => {
                self.store_into_destination(LiteralOrSource::Variable(*variable), destination);
                Ok(())
            }
            _ => Err(LinkError::UndefinedIdentifier(symbol.clone())),
        }
    }

    /// Looks up an existing location for a variable with the provided `name`.
    /// If an existing location is not found, new space will be allocated for
    /// it and returned.
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

    /// Creates a new temporary variable.
    ///
    /// Internally this simply uses a counter to create a new variable each time
    /// this is called named `$1`, `$2`, and so on.
    pub fn new_temporary_variable(&mut self) -> Variable {
        self.temporary_variables += 1;
        let variable = self.variable_index_from_name(&Symbol::from(
            format!("${}", self.temporary_variables).as_str(),
        ));
        variable
    }

    /// Returns the completed code block.
    #[must_use]
    pub fn finish(self) -> CodeBlock {
        CodeBlock {
            variables: self.variables.len(),
            code: self.ops,
        }
    }

    /// Begins a loop with the given `name`. The result of the loop will be
    /// stored in `result`. If the loop does not return a result, the
    /// destination will be untouched.
    pub fn begin_loop(&mut self, name: Option<Symbol>, result: Destination) -> LoopScope<'_, Self> {
        let break_label = self.new_label();
        let continue_label = self.new_label();
        self.labels.begin(LoopInfo {
            name,
            break_label,
            continue_label,
            loop_result: result,
        });
        LoopScope {
            owner: self,
            break_label,
            continue_label,
        }
    }

    /// Returns the collection of known variables.
    #[must_use]
    pub fn variables(&self) -> &HashMap<Symbol, Variable> {
        &self.variables
    }
}

/// A loop within a [`CodeBlockBuilder`].
#[must_use]
pub struct LoopScope<'a, T>
where
    T: BorrowMut<CodeBlockBuilder>,
{
    owner: &'a mut T,
    /// The label for a `break` operation.
    pub break_label: Label,
    /// The label for a `continue` operation.
    pub continue_label: Label,
}

impl<'a, T> LoopScope<'a, T>
where
    T: BorrowMut<CodeBlockBuilder>,
{
    /// Marks the next instruction as where the `break` operation should jump
    /// to.
    pub fn label_break(&mut self) {
        self.owner.borrow_mut().label(self.break_label);
    }

    /// Marks the next instruction as where the `continue` operation should jump
    /// to.
    pub fn label_continue(&mut self) {
        self.owner.borrow_mut().label(self.continue_label);
    }
}

impl<'a, T> Borrow<CodeBlockBuilder> for LoopScope<'a, T>
where
    T: BorrowMut<CodeBlockBuilder>,
{
    fn borrow(&self) -> &CodeBlockBuilder {
        (*self.owner).borrow()
    }
}

impl<'a, T> BorrowMut<CodeBlockBuilder> for LoopScope<'a, T>
where
    T: BorrowMut<CodeBlockBuilder>,
{
    fn borrow_mut(&mut self) -> &mut CodeBlockBuilder {
        self.owner.borrow_mut()
    }
}

impl<'a, T> Deref for LoopScope<'a, T>
where
    T: BorrowMut<CodeBlockBuilder>,
{
    type Target = CodeBlockBuilder;

    fn deref(&self) -> &Self::Target {
        self.borrow()
    }
}

impl<'a, T> DerefMut for LoopScope<'a, T>
where
    T: BorrowMut<CodeBlockBuilder>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.owner.borrow_mut()
    }
}

impl<'a, T> Drop for LoopScope<'a, T>
where
    T: BorrowMut<CodeBlockBuilder>,
{
    fn drop(&mut self) {
        self.labels.exit_block();
    }
}

#[derive(Debug, Default)]
struct CodeLabels {
    scopes: Vec<LoopInfo>,
}

impl CodeLabels {
    fn begin(&mut self, info: LoopInfo) {
        self.scopes.push(info);
    }

    fn exit_block(&mut self) {
        self.scopes.pop();
    }

    fn find(&self, name: Option<&Symbol>) -> Option<&LoopInfo> {
        if name.is_some() {
            self.scopes
                .iter()
                .rev()
                .find(|info| info.name.as_ref() == name)
        } else {
            self.scopes.last()
        }
    }
}

/// Information about a loop.
#[derive(Debug)]
pub struct LoopInfo {
    /// The name of the loop, if specified.
    pub name: Option<Symbol>,
    /// The label for the `break` operation of the loop.
    pub break_label: Label,
    /// The label for the `continue` operation of the loop.
    pub continue_label: Label,
    /// The desination to store the loops result into.
    pub loop_result: Destination,
}

/// A block of intermediate instructions.
#[derive(Debug)]
pub struct CodeBlock {
    /// The number of variables this code block uses.
    pub variables: usize,
    /// The list of instructions.
    pub code: Vec<Instruction>,
}

impl CodeBlock {
    /// Links the code block against `scope`, resolving all labels and function
    /// calls.
    #[allow(clippy::too_many_lines)]
    pub fn link<S>(&self, scope: &S) -> Result<crate::CodeBlock, LinkError>
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
            .collect::<Result<_, LinkError>>()
            .map(|instructions| crate::CodeBlock {
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
) -> Result<Option<crate::Instruction>, LinkError>
where
    S: Scope,
{
    Ok(Some(match op {
        Instruction::Add {
            left,
            right,
            destination,
        } => crate::Instruction::Add {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::Sub {
            left,
            right,
            destination,
        } => crate::Instruction::Sub {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::Multiply {
            left,
            right,
            destination,
        } => crate::Instruction::Multiply {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::Divide {
            left,
            right,
            destination,
        } => crate::Instruction::Divide {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::LogicalOr {
            left,
            right,
            destination,
        } => crate::Instruction::LogicalOr {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::LogicalAnd {
            left,
            right,
            destination,
        } => crate::Instruction::LogicalAnd {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::LogicalXor {
            left,
            right,
            destination,
        } => crate::Instruction::LogicalXor {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::BitwiseOr {
            left,
            right,
            destination,
        } => crate::Instruction::BitwiseOr {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::BitwiseAnd {
            left,
            right,
            destination,
        } => crate::Instruction::BitwiseAnd {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::BitwiseXor {
            left,
            right,
            destination,
        } => crate::Instruction::BitwiseXor {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::ShiftLeft {
            left,
            right,
            destination,
        } => crate::Instruction::ShiftLeft {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::ShiftRight {
            left,
            right,
            destination,
        } => crate::Instruction::ShiftRight {
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::Not { value, destination } => crate::Instruction::Not {
            value: value.instantiate::<S::Environment>(),
            destination: destination.into(),
        },
        Instruction::If {
            condition,
            false_jump_to,
        } => crate::Instruction::If {
            condition: condition.instantiate::<S::Environment>(),
            false_jump_to: labels[false_jump_to.0].expect("label not inserted"),
        },
        Instruction::JumpTo(label) => {
            crate::Instruction::JumpTo(labels[label.0].expect("label not inserted"))
        }
        Instruction::Label(_label) => return Ok(None), // Labels are no-ops
        Instruction::Compare {
            comparison,
            left,
            right,
            action,
        } => crate::Instruction::Compare {
            comparison: *comparison,
            left: left.instantiate::<S::Environment>(),
            right: right.instantiate::<S::Environment>(),
            action: action.link(labels)?,
        },
        Instruction::Push(value) => crate::Instruction::Push(value.instantiate::<S::Environment>()),
        Instruction::Return(value) => crate::Instruction::Return(
            value
                .as_ref()
                .map(LiteralOrSource::instantiate::<S::Environment>),
        ),
        Instruction::Load { value, variable } => crate::Instruction::Load {
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
                        .ok_or_else(|| LinkError::UndefinedFunction(symbol.clone()))
                })
                .transpose()?;
            crate::Instruction::Call {
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
        } => crate::Instruction::CallInstance {
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
        } => crate::Instruction::CallIntrinsic {
            intrinsic: *intrinsic,
            arg_count: *arg_count,
            destination: destination.into(),
        },
    }))
}

/// A scope for linking and compiling code.
pub trait Scope {
    /// The environment for this scope.
    ///
    /// This is used when instantiating literals as values.
    type Environment: Environment;

    /// Returns the vtable index of a function with the provided name.
    fn resolve_function_vtable_index(&self, name: &Symbol) -> Option<usize>;
    /// Invokes `callback` for each symbol defined in this scope.
    fn map_each_symbol(&self, callback: &mut impl FnMut(Symbol, ScopeSymbolKind));

    /// Defines a function with the provided name.
    fn define_function(&mut self, function: crate::Function) -> Option<usize>;

    /// Defines a persistent variable.
    ///
    /// This is used to enable interactive sessions.
    fn define_persistent_variable(&mut self, name: Symbol, variable: Variable);
}

impl Scope for () {
    type Environment = ();

    fn resolve_function_vtable_index(&self, _name: &Symbol) -> Option<usize> {
        None
    }

    fn map_each_symbol(&self, _callback: &mut impl FnMut(Symbol, ScopeSymbolKind)) {}

    fn define_function(&mut self, _function: crate::Function) -> Option<usize> {
        None
    }

    fn define_persistent_variable(&mut self, _name: Symbol, _variable: Variable) {}
}

/// The kind of a [`ScopeSymbol`].
#[derive(Debug)]
pub enum ScopeSymbolKind {
    /// The symbol is an argument passed into the executing function.
    Argument,
    /// The symbol is a local variable.
    Variable,
    /// The symbol is a function.
    Function,
}

/// A registered symbol.
#[derive(Debug)]
pub enum ScopeSymbol {
    /// An argument passed into the executing function.
    Argument(usize),
    /// A local variable.
    Variable(Variable),
    /// A function name.
    Function(Symbol),
}

/// A function, in its intermediate form.
#[derive(Debug)]
pub struct Function {
    /// The name of the function, if provided.
    pub name: Option<Symbol>,
    /// A list of names of arguments this function is expecting.
    pub args: Vec<Symbol>,
    /// The body of the function.
    pub body: CodeBlock,
}

impl Function {
    /// Returns a new function
    pub fn new(name: impl OptionalSymbol, args: Vec<Symbol>, body: CodeBlock) -> Self {
        Self {
            name: name.into_symbol(),
            args,
            body,
        }
    }

    /// Links this function against `scope`, returning a function that is ready
    /// to be executed.
    pub fn link<S>(&self, scope: &mut S) -> Result<crate::Function, LinkError>
    where
        S: Scope,
    {
        let name = self
            .name
            .clone()
            .expect("compiling an unnamed function into a context isn't allowed");
        let block = self.body.link(scope)?;
        if env::var("PRINT_IR").is_ok() {
            println!("{}", block.display_indented("  "));
        }
        let function = crate::Function {
            name,
            arg_count: self.args.len(),
            code: block.code,
            variable_count: block.variables,
        };
        Ok(function)
    }

    /// Links this function against `scope`, and registers the linked function
    /// with `scope`. The `usize` returned is the vtable index of the function.
    pub fn link_into<S>(&self, scope: &mut S) -> Result<usize, LinkError>
    where
        S: Scope,
    {
        let function = self.link(scope)?;

        let vtable_index = scope
            .define_function(function)
            .ok_or(LinkError::InvalidScopeOperation)?;
        Ok(vtable_index)
    }
}

/// A collection of functions and modules.
#[derive(Debug)]
pub struct Module {
    /// A list of functions defined in the module.
    pub vtable: Vec<Function>,
    /// A list of submodules.
    pub modules: Vec<Module>,
    /// The initialization function of this module, if any.
    pub init: Option<Function>,
}

impl Module {
    /// Returns a new module.
    #[must_use]
    pub fn new(vtable: Vec<Function>, modules: Vec<Module>, init: Option<Function>) -> Self {
        Self {
            vtable,
            modules,
            init,
        }
    }

    /// Runs all code in this unit in the passed context.
    pub fn load_into<'a, Output: FromStack, Env>(
        &self,
        context: &'a mut VirtualMachine<Env>,
    ) -> Result<Output, Error<'a, Env, Output>>
    where
        Env: Environment,
    {
        // // Process all modules first
        // for _module in &self.modules {
        //     todo!()
        // }

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
            function.link_into(context)?;
        }

        // Execute the module initializer if it exists
        if let Some(init) = &self.init {
            if env::var("PRINT_IR").is_ok() {
                println!("function init");
            }
            let vtable_index = init.link_into(context)?;
            context
                .run(
                    Cow::Owned(vec![crate::Instruction::Call {
                        vtable_index: Some(vtable_index),
                        arg_count: 0,
                        destination: crate::Destination::Stack,
                    }]),
                    0,
                )
                .map_err(Error::from)
        } else {
            Output::from_value(Value::Void).map_err(Error::from)
        }
    }
}

/// An error occurred while linking code.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum LinkError {
    /// An undefined function was encountered.
    UndefinedFunction(Symbol),
    /// An undefined identifier was encountered.
    UndefinedIdentifier(Symbol),
    /// An invalid label was used.
    InvalidLabel(Label),
    /// An invalid operation for the provided [`Scope`] was attempted.
    InvalidScopeOperation,
}

impl Display for LinkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LinkError::UndefinedFunction(symbol) => {
                write!(f, "undefined function: {symbol}")
            }
            LinkError::InvalidScopeOperation => {
                write!(f, "the scope used did not support a required operation")
            }
            LinkError::UndefinedIdentifier(symbol) => {
                write!(f, "undefined identifier: {symbol}")
            }
            LinkError::InvalidLabel(label) => {
                write!(f, "invalid label: {}", label.0)
            }
        }
    }
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
