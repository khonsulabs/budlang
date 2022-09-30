use std::{
    borrow::Cow,
    cmp::Ordering,
    collections::{HashMap, VecDeque},
    fmt::Display,
    marker::PhantomData,
};

use crate::{parser::parse, symbol::Symbol, Error};

/// A virtual machine instruction.
///
/// This enum contains all instructions that the virtual machine is able to
/// perform.
#[derive(Debug, Clone)]
pub enum Instruction {
    /// Pops left and right, and pushes the result of `left + right`.
    ///
    /// If this operation causes an overflow, [`Value::Void`] will be pushed
    /// instead.
    Add,
    /// Pops left and right, and pushes the result of `left - right`.
    ///
    /// If this operation causes an overflow, [`Value::Void`] will be pushed
    /// instead.
    Sub,
    /// Pops left and right, and pushes the result of `left * right`.
    ///
    /// If this operation causes an overflow, [`Value::Void`] will be pushed
    /// instead.
    Multiply,
    /// Pops left and right, and pushes the result of `left / right`.
    ///
    /// If this operation causes an overflow, [`Value::Void`] will be pushed
    /// instead.
    Divide,
    /// Pops `condition` and checks if
    /// [`condition.is_truthy()`](Value::is_truthy), jumping to the target
    /// instruction if false.
    ///
    /// If truthy, the virtual machine continues executing the next instruction
    /// in sequence.
    ///
    /// If not truthy, the virtual machine jumps to number `false_jump_to`. This
    /// number is the absolute number from the start of the set of instructions
    /// being executed.
    ///
    /// Jumping beyond the end of the function will not cause an error, but will
    /// instead cause the current function to return.
    If {
        /// The 0-based index of the instruction to jump to. This index is
        /// relative to the begining of the set of instructions being executed.
        false_jump_to: usize,
    },
    /// Jumps to the instruction number within the current function.
    ///
    /// This number is the absolute number from the start of the function being
    /// executed.
    ///
    /// Jumping beyond the end of the function will not cause an error, but will
    /// instead cause the current function to return.
    JumpTo(usize),
    /// Pops left and right and pushes the boolean result of the [`Comparison`].
    Compare(Comparison),
    /// Pushes a [`Value`] to the stack.
    Push(Value),
    /// Pushes a variable to the stack.
    ///
    /// Each function is allocated a fixed number of variables which are
    /// accessed using 0-based indexes. Attempting to use a variable index
    /// outside of the range allocated will cause a
    /// [`FaultKind::InvalidVariableIndex`] to be returned.
    PushVariable(usize),
    /// Pushes an argument to the stack.
    ///
    /// The value passed is a 0-based index to an argument that was passed to
    /// the function when called. Attempting to use an argument index
    /// larger than the number of arguments passed will cause a
    /// [`FaultKind::InvalidArgumentIndex`] to be returned.
    PushArg(usize),
    /// Pops a value from the stack and drops the value.
    ///
    /// Attempting to pop beyond the baseline of the currently executing set of
    /// instructions will cause a [`FaultKind::StackUnderflow`] to be returned.
    PopAndDrop,
    /// Returns from the current stack frame.
    Return,
    /// Pops a value from the stack and stores it into the variable index
    /// provided.
    ///
    /// Each function is allocated a fixed number of variables which are
    /// accessed using 0-based indexes. Attempting to use a variable index
    /// outside of the range allocated will cause a
    /// [`FaultKind::InvalidVariableIndex`] to be returned.
    PopToVariable(usize),
    /// Calls a function.
    ///
    /// When calling a function, values on the stack are "passed" to the
    /// function being pushed to the stack before calling the function. To
    /// ensure the correct number of arguments are taken even when variable
    /// argument lists are supported, the number of arguments is passed and
    /// controls the baseline of the stack.
    ///  
    /// Upon returning from a function call, the arguments will no longer be on
    /// the stack and a single value will always be returned. If the function
    /// did not push a value, [`Value::Void`] will be pushed.
    Call {
        /// The vtable index within the current module of the function to call.
        /// If None, the current function is called recursively.
        ///
        /// If a vtable index is provided but is beyond the number of functions
        /// registered to the current module, [`FaultKind::InvalidVtableIndex`]
        /// will be returned.
        vtable_index: Option<usize>,

        /// The number of arguments on the stack that should be used as
        /// arguments to this call.
        arg_count: usize,
    },
}

/// A method for comparing [`Value`]s.
#[derive(Debug, Clone, Copy)]
pub enum Comparison {
    /// Pushes true if left and right are equal. Otherwise, pushes false.
    Equal,
    /// Pushes true if left and right are not equal. Otherwise, pushes false.
    NotEqual,
    /// Pushes true if left is less than right. Otherwise, pushes false.
    LessThan,
    /// Pushes true if left is less than or equal to right. Otherwise, pushes false.
    LessThanOrEqual,
    /// Pushes true if left is greater than right. Otherwise, pushes false.
    GreaterThan,
    /// Pushes true if left is greater than or equal to right. Otherwise, pushes false.
    GreaterThanOrEqual,
}

/// A virtual machine function.
#[derive(Debug)]
pub struct Function {
    /// The number of arguments this function expects.
    pub arg_count: usize,
    /// The number of variables this function requests space for.
    pub variable_count: usize,
    /// The instructions that make up the function body.
    pub code: Vec<Instruction>,
}

/// A virtual machine value.
#[derive(Debug, Clone)]
pub enum Value {
    /// A signed 64-bit integer value.
    Integer(i64),
    /// A boolean representing true or false.
    Boolean(bool),
    /// A value representing the lack of a value.
    Void,
}

impl Value {
    /// Returns true if the value is considered truthy.
    ///
    /// | value type | condition     |
    /// |------------|---------------|
    /// | Integer    | value != 0    |
    /// | Boolean    | value is true |
    /// | Void       | always false  |
    #[must_use]
    pub fn is_truthy(&self) -> bool {
        match self {
            Value::Integer(value) => *value != 0,
            Value::Boolean(value) => *value,
            Value::Void => false,
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Integer(l0), Self::Integer(r0)) => l0 == r0,
            (Self::Boolean(l0), Self::Boolean(r0)) => l0 == r0,
            (Self::Void, Self::Void) => true,
            _ => false,
        }
    }
}

impl PartialEq<bool> for Value {
    fn eq(&self, other: &bool) -> bool {
        if let Self::Boolean(this) = self {
            this == other
        } else {
            false
        }
    }
}

impl PartialEq<i64> for Value {
    fn eq(&self, other: &i64) -> bool {
        if let Self::Integer(this) = self {
            this == other
        } else {
            false
        }
    }
}

#[derive(Debug, Default)]
struct Module {
    contents: HashMap<Symbol, ModuleItem>,
    vtable: Vec<Function>,
}

impl Module {
    // #[must_use]
    // pub fn with_function(mut self, name: impl Into<Symbol>, function: Function) -> Self {
    //     self.define_function(name, function);
    //     self
    // }

    pub fn define_function(&mut self, name: impl Into<Symbol>, function: Function) -> usize {
        let vtable_index = self.vtable.len();
        self.contents
            .insert(name.into(), ModuleItem::Function(vtable_index));
        self.vtable.push(function);
        vtable_index
    }
}

#[derive(Debug)]
enum ModuleItem {
    Function(usize),
    // Module(Module),
}

/// A Bud virtual machine instance.
///
/// Each instance of this type has its own sandboxed environment. Its stack
/// space, function declarations, and [`Environment`] are unique from all other
/// instances of Bud with the exception that [`Symbol`]s are tracked globally.
#[derive(Debug, Default)]
pub struct Bud<Env> {
    stack: Vec<Value>,
    local_module: Module,
    environment: Env,
}

impl Bud<()> {
    /// Returns a default instance of Bud with no custom [`Environment`]
    #[must_use]
    pub fn empty() -> Self {
        Self::new(())
    }
}

impl<Env> Bud<Env>
where
    Env: Environment,
{
    /// Returns a new instance with the provided environment.
    pub fn new(environment: Env) -> Self {
        Self {
            environment,
            stack: Vec::new(),
            local_module: Module::default(),
        }
    }

    /// Returns a reference to the environment for this instance.
    pub fn environment(&self) -> &Env {
        &self.environment
    }

    /// Returns a mutable refernce to the environment for this instance.
    pub fn environment_mut(&mut self) -> &mut Env {
        &mut self.environment
    }

    /// Registers a function with the provided name and returns self. This is a
    /// builder-style function.
    #[must_use]
    pub fn with_function(mut self, name: impl Into<Symbol>, function: Function) -> Self {
        self.define_function(name, function);
        self
    }

    /// Defines a function with the provided name.
    pub fn define_function(&mut self, name: impl Into<Symbol>, function: Function) -> usize {
        self.local_module.define_function(name, function)
    }

    /// Runs a set of instructions.
    pub fn run<'a, Output: FromStack>(
        &'a mut self,
        operations: Cow<'a, [Instruction]>,
    ) -> Result<Output, Fault<'a, Env, Output>> {
        let return_offset = self.stack.len();
        match (StackFrame {
            module: &self.local_module,
            stack: &mut self.stack,
            environment: &mut self.environment,
            return_offset,
            vtable_index: None,
            variables_offset: 0,
            operation_index: 0,
            arg_offset: 0,
            _output: PhantomData,
        }
        .execute_operations(&operations))
        {
            Err(Fault {
                kind: FaultKind::Paused(paused_evaluation),
                stack,
            }) => {
                let paused_evaluation = PausedExecution {
                    context: Some(self),
                    operations: Some(operations),
                    stack: paused_evaluation.stack,
                    _return: PhantomData,
                };
                return Err(Fault {
                    kind: FaultKind::Paused(paused_evaluation),
                    stack,
                });
            }
            other => other?,
        }
        Output::from_stack(self)
    }

    fn resume<'a, Output: FromStack>(
        &'a mut self,
        operations: Cow<'a, [Instruction]>,
        mut paused_stack: VecDeque<PausedFrame>,
    ) -> Result<Output, Fault<'a, Env, Output>> {
        let first_frame = paused_stack.pop_front().expect("at least one frame");
        match (StackFrame {
            module: &self.local_module,
            stack: &mut self.stack,
            environment: &mut self.environment,
            return_offset: first_frame.return_offset,
            vtable_index: first_frame.vtable_index,
            variables_offset: first_frame.variables_offset,
            operation_index: first_frame.operation_index,
            arg_offset: first_frame.arg_offset,
            _output: PhantomData,
        }
        .resume_executing_execute_operations(&operations, paused_stack))
        {
            Ok(()) => {}
            Err(Fault {
                kind: FaultKind::Paused(paused_evaluation),
                stack,
            }) => {
                let paused_evaluation = PausedExecution {
                    context: Some(self),
                    operations: Some(operations),
                    stack: paused_evaluation.stack,
                    _return: PhantomData,
                };
                return Err(Fault {
                    kind: FaultKind::Paused(paused_evaluation),
                    stack,
                });
            }
            Err(other) => return Err(other),
        }
        Output::from_stack(self)
    }

    /// Compiles `source` and executes it in this context. Any declarations will
    /// persist in the virtual machine.
    pub fn run_source<Output: FromStack>(
        &mut self,
        source: &str,
    ) -> Result<Output, Error<'_, Env, Output>> {
        let unit = parse(source)?;
        unit.compile().execute_in(self)
    }

    /// Returns the vtable index of a function with the provided name.
    pub fn resolve_function_vtable_index(&self, name: &Symbol) -> Option<usize> {
        if let Some(module_item) = self.local_module.contents.get(name) {
            match module_item {
                ModuleItem::Function(index) => Some(*index),
                // ModuleItem::Module(_) => None,
            }
        } else {
            None
        }
    }
}

enum FlowControl {
    Return,
    JumpTo(usize),
}

#[derive(Debug)]
struct StackFrame<'a, Env, Output> {
    module: &'a Module,
    stack: &'a mut Vec<Value>,
    environment: &'a mut Env,
    // Each stack frame cannot pop below this offset.
    return_offset: usize,
    variables_offset: usize,
    arg_offset: usize,

    vtable_index: Option<usize>,
    operation_index: usize,

    _output: PhantomData<Output>,
}

impl<'a, Env, Output> StackFrame<'a, Env, Output>
where
    Env: Environment,
{
    fn resume_executing_execute_operations(
        &mut self,
        operations: &[Instruction],
        mut resume_from: VecDeque<PausedFrame>,
    ) -> Result<(), Fault<'static, Env, Output>> {
        if let Some(frame_to_resume) = resume_from.pop_front() {
            // We were calling a function when this happened. We need to finish the call.
            let vtable_index = frame_to_resume.vtable_index.expect("always have a vtable");
            let function = &self.module.vtable[vtable_index]; // TODO this module isn't necessarily right, but we don't really support modules.
            let mut running_frame = StackFrame {
                module: self.module,
                stack: self.stack,
                environment: self.environment,
                return_offset: frame_to_resume.return_offset,
                variables_offset: frame_to_resume.variables_offset,
                arg_offset: frame_to_resume.arg_offset,
                vtable_index: frame_to_resume.vtable_index,
                operation_index: frame_to_resume.operation_index,
                _output: PhantomData,
            };
            match running_frame.resume_executing_execute_operations(&function.code, resume_from) {
                Ok(_) => {}
                Err(Fault {
                    kind: FaultKind::Paused(mut paused),
                    stack,
                }) => {
                    paused.stack.push_front(PausedFrame {
                        return_offset: self.return_offset,
                        arg_offset: self.arg_offset,
                        variables_offset: self.variables_offset,
                        vtable_index: self.vtable_index,
                        operation_index: self.operation_index,
                    });
                    return Err(Fault {
                        kind: FaultKind::Paused(paused),
                        stack,
                    });
                }
                Err(err) => return Err(err),
            };

            // Remove the args, which sit between the stack and the return value
            self.stack
                .drain(frame_to_resume.arg_offset..frame_to_resume.return_offset);
        }

        self.execute_operations(operations)
    }
    fn execute_operations(
        &mut self,
        operations: &[Instruction],
    ) -> Result<(), Fault<'static, Env, Output>> {
        loop {
            if matches!(self.environment.step(), ExecutionBehavior::Pause) {
                let mut stack = VecDeque::new();
                stack.push_front(PausedFrame {
                    return_offset: self.return_offset,
                    arg_offset: self.arg_offset,
                    variables_offset: self.variables_offset,
                    vtable_index: self.vtable_index,
                    operation_index: self.operation_index,
                });
                return Err(Fault {
                    kind: FaultKind::Paused(PausedExecution {
                        context: None,
                        operations: None,
                        stack,
                        _return: PhantomData,
                    }),
                    stack: vec![FaultStackFrame {
                        vtable_index: self.vtable_index,
                        instruction_index: self.operation_index,
                    }],
                });
            }

            let operation = operations.get(self.operation_index);
            let operation = match operation {
                Some(operation) => operation,
                None => {
                    // Implicit return;
                    return Ok(());
                }
            };
            self.operation_index += 1;
            match self.execute_operation(operation) {
                Ok(Some(FlowControl::JumpTo(op_index))) => {
                    self.operation_index = op_index;
                }
                Ok(Some(FlowControl::Return)) => {
                    return Ok(());
                }
                Ok(None) => {}
                Err(mut fault) => {
                    if let FaultKind::Paused(paused_frame) = &mut fault.kind {
                        paused_frame.stack.push_front(PausedFrame {
                            return_offset: self.return_offset,
                            arg_offset: self.arg_offset,
                            variables_offset: self.variables_offset,
                            vtable_index: self.vtable_index,
                            operation_index: self.operation_index,
                        });
                    }
                    fault.stack.insert(
                        0,
                        FaultStackFrame {
                            vtable_index: self.vtable_index,
                            instruction_index: self.operation_index - 1,
                        },
                    );
                    return Err(fault);
                }
            }
        }
    }

    #[allow(clippy::too_many_lines)] // TODO I agree, but staring at a wall of yellow underlines is horrible.
    fn execute_operation(
        &mut self,
        operation: &Instruction,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        match operation {
            Instruction::JumpTo(instruction_index) => {
                Ok(Some(FlowControl::JumpTo(*instruction_index)))
            }
            Instruction::Add => {
                let (left, right) = self.pop_pair()?;
                let result = match (left, right) {
                    (Value::Integer(left), Value::Integer(right)) => {
                        left.checked_add(right).map_or(Value::Void, Value::Integer)
                    }
                    _ => todo!(),
                };
                self.stack.push(result);
                Ok(None)
            }
            Instruction::Sub => {
                let (left, right) = self.pop_pair()?;
                let result = match (left, right) {
                    (Value::Integer(left), Value::Integer(right)) => {
                        left.checked_sub(right).map_or(Value::Void, Value::Integer)
                    }
                    _ => todo!(),
                };
                self.stack.push(result);
                Ok(None)
            }
            Instruction::Multiply => {
                let (left, right) = self.pop_pair()?;
                let result = match (left, right) {
                    (Value::Integer(left), Value::Integer(right)) => {
                        left.checked_mul(right).map_or(Value::Void, Value::Integer)
                    }
                    _ => todo!(),
                };
                self.stack.push(result);
                Ok(None)
            }
            Instruction::Divide => {
                let (left, right) = self.pop_pair()?;
                let result = match (left, right) {
                    (Value::Integer(left), Value::Integer(right)) => {
                        left.checked_div(right).map_or(Value::Void, Value::Integer)
                    }
                    _ => todo!(),
                };
                self.stack.push(result);
                Ok(None)
            }
            Instruction::If {
                false_jump_to: false_jump_to_label,
            } => {
                let value_to_check = self.pop()?;
                if value_to_check.is_truthy() {
                    Ok(None)
                } else {
                    Ok(Some(FlowControl::JumpTo(*false_jump_to_label)))
                }
            }
            Instruction::Compare(comparison) => {
                let (left, right) = self.pop_pair()?;
                let cmp_result = match (left, right) {
                    (Value::Integer(left), Value::Integer(right)) => left.cmp(&right),
                    _ => todo!(),
                };
                let result = matches!(
                    (comparison, cmp_result),
                    (Comparison::Equal, Ordering::Equal)
                        | (Comparison::NotEqual, Ordering::Greater | Ordering::Less)
                        | (Comparison::GreaterThan, Ordering::Greater)
                        | (
                            Comparison::GreaterThanOrEqual,
                            Ordering::Greater | Ordering::Equal
                        )
                        | (Comparison::LessThan, Ordering::Less)
                        | (
                            Comparison::LessThanOrEqual,
                            Ordering::Less | Ordering::Equal
                        )
                );
                self.stack.push(Value::Boolean(result));
                Ok(None)
            }
            Instruction::Push(value) => {
                self.stack.push(value.clone());
                Ok(None)
            }
            Instruction::PushVariable(variable) => {
                if let Some(stack_offset) = self.variables_offset.checked_add(*variable) {
                    if stack_offset < self.return_offset {
                        let value = self.stack[stack_offset].clone();
                        self.stack.push(value);
                        return Ok(None);
                    }
                }
                Err(Fault::from(FaultKind::InvalidVariableIndex))
            }
            Instruction::PushArg(arg_index) => {
                if let Some(stack_offset) = self.arg_offset.checked_add(*arg_index) {
                    if stack_offset < self.variables_offset {
                        let value = self.stack[stack_offset].clone();
                        self.stack.push(value);
                        return Ok(None);
                    }
                }
                Err(Fault::from(FaultKind::InvalidArgumentIndex))
            }
            Instruction::PopAndDrop => {
                self.pop()?;
                Ok(None)
            }
            Instruction::Return => Ok(Some(FlowControl::Return)),
            Instruction::PopToVariable(variable) => {
                let value = self.stack.pop().ok_or_else(Fault::stack_underflow)?;
                if let Some(stack_offset) = self.variables_offset.checked_add(*variable) {
                    if stack_offset < self.return_offset {
                        self.stack[stack_offset] = value;
                        return Ok(None);
                    }
                }
                Ok(None)
            }
            Instruction::Call {
                vtable_index,
                arg_count,
            } => {
                let vtable_index = vtable_index
                    .or(self.vtable_index)
                    .ok_or(FaultKind::InvalidVtableIndex)?;
                let function = &self
                    .module
                    .vtable
                    .get(vtable_index)
                    .ok_or(FaultKind::InvalidVtableIndex)?;

                assert_eq!(function.arg_count, *arg_count);

                let variables_offset = self.stack.len();
                let return_offset = variables_offset + function.variable_count;
                let arg_offset = variables_offset - function.arg_count;
                if function.variable_count > 0 {
                    self.stack
                        .resize(return_offset + function.variable_count, Value::Void);
                }

                StackFrame {
                    module: self.module,
                    stack: self.stack,
                    environment: self.environment,
                    return_offset,
                    variables_offset,
                    arg_offset,
                    vtable_index: Some(vtable_index),
                    operation_index: 0,
                    _output: PhantomData,
                }
                .execute_operations(&function.code)?;

                // Remove the args, which sit between the stack and the return value
                self.stack.drain(arg_offset..return_offset);

                Ok(None)
            }
        }
    }

    fn safe_pop(&mut self) -> Option<Value> {
        if self.stack.len() > self.return_offset {
            self.stack.pop()
        } else {
            None
        }
    }

    fn pop(&mut self) -> Result<Value, Fault<'static, Env, Output>> {
        self.safe_pop().ok_or_else(Fault::stack_underflow)
    }

    fn pop_pair(&mut self) -> Result<(Value, Value), Fault<'static, Env, Output>> {
        if let (Some(first), Some(second)) = (self.safe_pop(), self.safe_pop()) {
            Ok((first, second))
        } else {
            Err(Fault::stack_underflow())
        }
    }
}

/// An unexpected event occurred while executing the virtual machine.
#[derive(Debug)]
pub struct Fault<'a, Env, ReturnType> {
    /// The kind of fault this is.
    pub kind: FaultKind<'a, Env, ReturnType>,
    /// The stack trace of the virtual machine when the fault was raised.
    pub stack: Vec<FaultStackFrame>,
}

impl<'a, Env, ReturnType> Fault<'a, Env, ReturnType> {
    fn stack_underflow() -> Self {
        Self::from(FaultKind::StackUnderflow)
    }
}
impl<'a, Env, ReturnType> From<FaultKind<'a, Env, ReturnType>> for Fault<'a, Env, ReturnType> {
    fn from(kind: FaultKind<'a, Env, ReturnType>) -> Self {
        Self {
            kind,
            stack: Vec::default(),
        }
    }
}

impl<'a, Env, ReturnType> std::error::Error for Fault<'a, Env, ReturnType>
where
    Env: std::fmt::Debug,
    ReturnType: std::fmt::Debug,
{
}

impl<'a, Env, ReturnType> Display for Fault<'a, Env, ReturnType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.kind, f)
    }
}

/// An unexpected event within the virtual machine.
#[derive(Debug)]
pub enum FaultKind<'a, Env, ReturnType> {
    /// An attempt to pop a value off of the stack was made when no values were
    /// present in the current code's stack frame.
    StackUnderflow,
    /// Execution was paused by the [`Environment`] as a result of returning
    /// [`ExecutionBehavior::Pause`] from [`Environment::step`].
    ///
    /// The contained [`PausedExecution`] can be used to resume executing the
    /// code.
    Paused(PausedExecution<'a, Env, ReturnType>),
    /// An invalid variable index was used.
    InvalidVariableIndex,
    /// An invalid argument index was used.
    InvalidArgumentIndex,
    /// An invalid vtable index was used.
    InvalidVtableIndex,
}

impl<'a, Env, ReturnType> std::error::Error for FaultKind<'a, Env, ReturnType>
where
    Env: std::fmt::Debug,
    ReturnType: std::fmt::Debug,
{
}

impl<'a, Env, ReturnType> Display for FaultKind<'a, Env, ReturnType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FaultKind::StackUnderflow => f.write_str("stack popped but no values present"),
            FaultKind::Paused(_) => f.write_str("execution paused"),
            FaultKind::InvalidVariableIndex => {
                f.write_str("a variable index was outside of the range allocated for the function")
            }
            FaultKind::InvalidArgumentIndex => f.write_str(
                "an argument index was beyond the number of arguments passed to the function",
            ),
            FaultKind::InvalidVtableIndex => f.write_str(
                "a vtable index was beyond the number functions registerd in the current module",
            ),
        }
    }
}

/// A stack frame entry of a [`Fault`].
#[derive(Debug)]
pub struct FaultStackFrame {
    /// The vtable index of the function being executed. If None, the
    /// instructions being executed were passed directly into [`Bud::run()`].
    pub vtable_index: Option<usize>,
    /// The index of the instruction that was executing when this fault was
    /// raised.
    pub instruction_index: usize,
}

/// A paused code execution.
#[derive(Debug)]
pub struct PausedExecution<'a, Env, ReturnType> {
    context: Option<&'a mut Bud<Env>>,
    operations: Option<Cow<'a, [Instruction]>>,
    stack: VecDeque<PausedFrame>,
    _return: PhantomData<ReturnType>,
}

impl<'a, Env, ReturnType> PausedExecution<'a, Env, ReturnType>
where
    ReturnType: FromStack,
{
    /// Returns a reference to the [`Environment`] from the virtual machine that
    /// is paused.
    #[must_use]
    pub fn environment(&self) -> &Env {
        &self.context.as_ref().expect("context missing").environment
    }

    /// Returns a mutable reference to the [`Environment`] from the virtual
    /// machine that is paused.
    #[must_use]
    pub fn environment_mut(&mut self) -> &mut Env {
        &mut self.context.as_mut().expect("context missing").environment
    }

    /// Resumes executing the virtual machine.
    pub fn resume(self) -> Result<ReturnType, Fault<'a, Env, ReturnType>>
    where
        Env: Environment,
    {
        let context = self
            .context
            .expect("context should be present before returning to the user");
        let operations = self
            .operations
            .expect("operations should be present before returning to the user");
        context.resume(operations, self.stack)
    }
}

#[derive(Debug)]
struct PausedFrame {
    return_offset: usize,
    arg_offset: usize,
    variables_offset: usize,

    vtable_index: Option<usize>,
    operation_index: usize,
}

/// A type that can be constructed from popping from the virtual machine stack.
pub trait FromStack: Sized {
    /// Returns an instance constructing from the stack.
    fn from_stack<Env>(stack: &mut Bud<Env>) -> Result<Self, Fault<'static, Env, Self>>;
}

impl FromStack for Value {
    fn from_stack<Env>(stack: &mut Bud<Env>) -> Result<Self, Fault<'static, Env, Self>> {
        stack.stack.pop().ok_or_else(Fault::stack_underflow)
    }
}

impl FromStack for i64 {
    fn from_stack<Env>(stack: &mut Bud<Env>) -> Result<Self, Fault<'static, Env, Self>> {
        match stack.stack.pop().ok_or_else(Fault::stack_underflow)? {
            Value::Integer(integer) => Ok(integer),
            _ => todo!("type mismatch"),
        }
    }
}

impl FromStack for () {
    fn from_stack<Env>(_stack: &mut Bud<Env>) -> Result<Self, Fault<'static, Env, Self>> {
        Ok(())
    }
}

/// Customizes the behavior of a virtual machine instance.
pub trait Environment: 'static {
    /// Called once before each instruction is executed.
    ///
    /// If [`ExecutionBehavior::Continue`] is returned, the next instruction
    /// will be exected.
    ///
    /// If [`ExecutionBehavior::Pause`] is returned, the virtual machine is
    /// paused and a [`FaultKind::Paused`] is raised. If the execution is
    /// resumed, the first function call will be before executing the same
    /// instruction as the one when [`ExecutionBehavior::Pause`] was called.
    fn step(&mut self) -> ExecutionBehavior;
}

impl Environment for () {
    #[inline]
    fn step(&mut self) -> ExecutionBehavior {
        ExecutionBehavior::Continue
    }
}

/// An [`Environment`] that allows executing an amount of instructions before
/// pausing the virtual machine.
#[derive(Debug, Default)]
#[must_use]
pub struct Budgeted(usize);

impl Budgeted {
    /// Returns a new instance with the provided initial budget.
    pub const fn new(initial_budget: usize) -> Self {
        Self(initial_budget)
    }

    /// Returns the current balance of the budget.
    #[must_use]
    pub const fn balance(&self) -> usize {
        self.0
    }

    /// Adds an additional budget. This value will saturate `usize` instead of
    /// panicking or overflowing.
    pub fn add_budget(&mut self, additional_budget: usize) {
        self.0 = self.0.saturating_add(additional_budget);
    }
}

impl Environment for Budgeted {
    #[inline]
    fn step(&mut self) -> ExecutionBehavior {
        if self.0 > 0 {
            self.0 -= 1;
            ExecutionBehavior::Continue
        } else {
            ExecutionBehavior::Pause
        }
    }
}

/// The virtual machine behavior returned from [`Environment::step()`].
pub enum ExecutionBehavior {
    /// The virtual machine should continue executing.
    Continue,
    /// The virtual machine should pause before the next instruction is
    /// executed.
    Pause,
}

#[test]
fn budget() {
    let mut context = Bud::new(Budgeted::new(0));
    let mut fault = context
        .run::<i64>(Cow::Borrowed(&[
            Instruction::Push(Value::Integer(1)),
            Instruction::Push(Value::Integer(2)),
            Instruction::Add,
        ]))
        .unwrap_err();
    let output = loop {
        println!("Paused");
        let mut pending = match fault.kind {
            FaultKind::Paused(pending) => pending,
            error => unreachable!("unexpected error: {error}"),
        };
        pending.environment_mut().add_budget(1);

        fault = match pending.resume() {
            Ok(result) => break result,
            Err(err) => err,
        };
    };

    assert_eq!(output, 3);
}

#[test]
fn budget_with_frames() {
    let test = Function {
        arg_count: 1,
        variable_count: 0,
        code: vec![
            Instruction::PushArg(0),
            Instruction::If { false_jump_to: 12 },
            Instruction::Push(Value::Integer(1)),
            Instruction::Push(Value::Integer(2)),
            Instruction::Add,
            Instruction::Push(Value::Integer(3)),
            Instruction::Add,
            Instruction::Push(Value::Integer(4)),
            Instruction::Add,
            Instruction::Push(Value::Integer(5)),
            Instruction::Add,
            Instruction::Return,
            // If we were passed false, call ourself twice.
            Instruction::Push(Value::Boolean(true)),
            Instruction::Call {
                vtable_index: None,
                arg_count: 1,
            },
            Instruction::Push(Value::Boolean(true)),
            Instruction::Call {
                vtable_index: None,
                arg_count: 1,
            },
            Instruction::Add, // should produce 30
        ],
    };
    let mut context = Bud::new(Budgeted::new(0)).with_function("test", test);
    let mut fault = context
        .run::<i64>(Cow::Borrowed(&[
            Instruction::Push(Value::Boolean(false)),
            Instruction::Call {
                vtable_index: Some(0),
                arg_count: 1,
            },
        ]))
        .unwrap_err();
    let output = loop {
        println!("Paused");
        let mut pending = match fault.kind {
            FaultKind::Paused(pending) => pending,
            error => unreachable!("unexpected error: {error}"),
        };
        dbg!(&pending.stack);
        pending.environment_mut().add_budget(1);

        fault = match pending.resume() {
            Ok(result) => break result,
            Err(err) => err,
        };
    };

    assert_eq!(output, 30);
}

#[test]
fn invalid_variables() {
    let test = Function {
        arg_count: 0,
        variable_count: 0,
        code: vec![Instruction::PushVariable(0)],
    };
    let mut context = Bud::empty().with_function("test", test);
    assert!(matches!(
        context
            .run::<i64>(Cow::Borrowed(&[Instruction::Call {
                vtable_index: Some(0),
                arg_count: 0,
            }]))
            .unwrap_err()
            .kind,
        FaultKind::InvalidVariableIndex
    ));
}

#[test]
fn invalid_argument() {
    let test = Function {
        arg_count: 0,
        variable_count: 0,
        code: vec![Instruction::PushArg(0)],
    };
    let mut context = Bud::empty().with_function("test", test);
    assert!(matches!(
        context
            .run::<i64>(Cow::Borrowed(&[Instruction::Call {
                vtable_index: Some(0),
                arg_count: 0,
            }]))
            .unwrap_err()
            .kind,
        FaultKind::InvalidArgumentIndex
    ));
}

#[test]
fn invalid_vtable_index() {
    let mut context = Bud::empty();
    assert!(matches!(
        context
            .run::<i64>(Cow::Borrowed(&[Instruction::Call {
                vtable_index: Some(0),
                arg_count: 0,
            }]))
            .unwrap_err()
            .kind,
        FaultKind::InvalidVtableIndex
    ));
}
