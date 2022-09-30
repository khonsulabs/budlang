use std::{
    borrow::Cow,
    cmp::Ordering,
    collections::{HashMap, VecDeque},
    fmt::Display,
    marker::PhantomData,
};

use crate::{parser::parse, symbol::Symbol, Error};

#[derive(Debug, Clone)]
pub enum Operation {
    Add,
    Sub,
    Multiply,
    Divide,
    If {
        false_jump_to: usize,
    },
    JumpTo(usize),
    Compare(Comparison),
    Push(Value),
    PushVariable(usize),
    PushArg(usize),
    Pop,
    Return,
    PopToVariable {
        variable_index: usize,
    },
    Call {
        vtable_index: Option<usize>,
        arg_count: usize,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum Comparison {
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
}

#[derive(Debug)]
pub struct Function {
    pub arg_count: usize,
    pub variable_count: usize,
    pub ops: Vec<Operation>,
}

#[derive(Debug, Clone)]
pub enum Value {
    Integer(i64),
    Void,
    Boolean(bool),
}

impl Value {
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
pub struct Module {
    contents: HashMap<Symbol, ModuleItem>,
    vtable: Vec<Function>,
}

impl Module {
    pub fn with_function(mut self, name: impl Into<Symbol>, function: Function) -> Self {
        self.define_function(name, function);
        self
    }

    pub fn define_function(&mut self, name: impl Into<Symbol>, function: Function) -> usize {
        let vtable_index = self.vtable.len();
        self.contents
            .insert(name.into(), ModuleItem::Function(vtable_index));
        self.vtable.push(function);
        vtable_index
    }

    // /// Imports a module.
    // pub fn with_code_unit(mut self, name: impl Into<Symbol>, code_unit: ast::CodeUnit) -> Self {
    //     todo!()
    // }
}

#[derive(Debug)]
pub enum ModuleItem {
    Function(usize),
    Module(Module),
}

#[derive(Debug, Default)]
pub struct Context<Env> {
    stack: Vec<Value>,
    local_module: Module,
    environment: Env,
}

impl Context<()> {
    pub fn empty() -> Self {
        Self::new(())
    }
}

impl<Env> Context<Env>
where
    Env: Environment,
{
    pub fn new(environment: Env) -> Self {
        Self {
            environment,
            stack: Vec::new(),
            local_module: Module::default(),
        }
    }

    pub fn environment(&self) -> &Env {
        &self.environment
    }

    pub fn environment_mut(&mut self) -> &mut Env {
        &mut self.environment
    }

    pub fn with_function(mut self, name: impl Into<Symbol>, function: Function) -> Self {
        self.define_function(name, function);
        self
    }

    pub fn define_function(&mut self, name: impl Into<Symbol>, function: Function) -> usize {
        self.local_module.define_function(name, function)
    }

    pub fn run<'a, Output: FromStack>(
        &'a mut self,
        operations: Cow<'a, [Operation]>,
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
                let paused_evaluation = PausedEvaluation {
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
        operations: Cow<'a, [Operation]>,
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
                let paused_evaluation = PausedEvaluation {
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

    pub fn run_source<Output: FromStack>(
        &mut self,
        source: &str,
    ) -> Result<Output, Error<'_, Env, Output>> {
        let unit = parse(source)?;
        unit.compile().execute_in(self)
    }

    pub fn resolve_function_index(&self, symbol: &Symbol) -> Option<usize> {
        if let Some(module_item) = self.local_module.contents.get(symbol) {
            match module_item {
                ModuleItem::Function(index) => Some(*index),
                ModuleItem::Module(_) => None,
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
    arg_offset: usize,
    variables_offset: usize,

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
        operations: &[Operation],
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
            match running_frame.resume_executing_execute_operations(&function.ops, resume_from) {
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
        operations: &[Operation],
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
                    kind: FaultKind::Paused(PausedEvaluation {
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

    fn execute_operation(
        &mut self,
        operation: &Operation,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        match operation {
            Operation::JumpTo(instruction_index) => {
                Ok(Some(FlowControl::JumpTo(*instruction_index)))
            }
            Operation::Add => {
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
            Operation::Sub => {
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
            Operation::Multiply => {
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
            Operation::Divide => {
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
            Operation::If {
                false_jump_to: false_jump_to_label,
            } => {
                let value_to_check = self.pop()?;
                if value_to_check.is_truthy() {
                    Ok(None)
                } else {
                    Ok(Some(FlowControl::JumpTo(*false_jump_to_label)))
                }
            }
            Operation::Compare(comparison) => {
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
            Operation::Push(value) => {
                self.stack.push(value.clone());
                Ok(None)
            }
            Operation::PushVariable(variable) => {
                let value = self.stack[self.variables_offset + *variable].clone();
                self.stack.push(value);
                Ok(None)
            }
            Operation::PushArg(stack_offset) => {
                let value = self.stack[self.arg_offset + *stack_offset].clone();
                self.stack.push(value);
                Ok(None)
            }
            Operation::Pop => {
                self.pop()?;
                Ok(None)
            }
            Operation::Return => Ok(Some(FlowControl::Return)),
            Operation::PopToVariable { variable_index } => {
                let value = self.stack.pop().ok_or_else(Fault::stack_underflow)?;
                self.stack[self.variables_offset + variable_index] = value;
                Ok(None)
            }
            Operation::Call {
                vtable_index,
                arg_count,
            } => {
                let vtable_index = vtable_index
                    .or(self.vtable_index)
                    .expect("invalid vtable index");
                let function = &self.module.vtable[vtable_index];

                // let function = self.local_module.vtable[vtable_index].clone();
                // println!("Call {vtable_index:?} with {arg_count} args");

                assert_eq!(function.arg_count, *arg_count);
                // assert_eq!(function.return_count, *return_count);

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
                .execute_operations(&function.ops)?;

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

#[derive(Debug)]
pub struct Fault<'a, Env, ReturnType> {
    pub kind: FaultKind<'a, Env, ReturnType>,
    pub stack: Vec<FaultStackFrame>,
}

impl<'a, Env, ReturnType> Fault<'a, Env, ReturnType> {
    fn stack_underflow() -> Self {
        Self {
            stack: Vec::default(),
            kind: FaultKind::StackUnderflow,
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

#[derive(Debug)]
pub enum FaultKind<'a, Env, ReturnType> {
    StackUnderflow,
    Paused(PausedEvaluation<'a, Env, ReturnType>),
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
        }
    }
}

#[derive(Debug)]
pub struct FaultStackFrame {
    pub vtable_index: Option<usize>,
    pub instruction_index: usize,
}

#[derive(Debug)]
pub struct PausedEvaluation<'a, Env, ReturnType> {
    context: Option<&'a mut Context<Env>>,
    operations: Option<Cow<'a, [Operation]>>,
    stack: VecDeque<PausedFrame>,
    _return: PhantomData<ReturnType>,
}

impl<'a, Env, ReturnType> PausedEvaluation<'a, Env, ReturnType>
where
    ReturnType: FromStack,
{
    pub fn context(&self) -> &Env {
        &self.context.as_ref().expect("context missing").environment
    }

    pub fn environment_mut(&mut self) -> &mut Env {
        &mut self.context.as_mut().expect("context missing").environment
    }

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

pub trait FromStack: Sized {
    fn from_stack<Env>(stack: &mut Context<Env>) -> Result<Self, Fault<'static, Env, Self>>;
}

impl FromStack for Value {
    fn from_stack<Env>(stack: &mut Context<Env>) -> Result<Self, Fault<'static, Env, Self>> {
        stack.stack.pop().ok_or_else(Fault::stack_underflow)
    }
}

impl FromStack for i64 {
    fn from_stack<Env>(stack: &mut Context<Env>) -> Result<Self, Fault<'static, Env, Self>> {
        match stack.stack.pop().ok_or_else(Fault::stack_underflow)? {
            Value::Integer(integer) => Ok(integer),
            _ => todo!("type mismatch"),
        }
    }
}

impl FromStack for () {
    fn from_stack<Env>(_stack: &mut Context<Env>) -> Result<Self, Fault<'static, Env, Self>> {
        Ok(())
    }
}

pub trait Environment: 'static {
    fn step(&mut self) -> ExecutionBehavior;
}

impl Environment for () {
    #[inline]
    fn step(&mut self) -> ExecutionBehavior {
        ExecutionBehavior::Continue
    }
}

#[derive(Debug, Default)]
pub struct Budgeted(usize);

impl Budgeted {
    pub const fn new(initial_budget: usize) -> Self {
        Self(initial_budget)
    }

    pub const fn balance(&self) -> usize {
        self.0
    }

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

pub enum ExecutionBehavior {
    Continue,
    Pause,
}

#[test]
fn budget() {
    let mut context = Context::new(Budgeted::new(0));
    let mut fault = context
        .run::<i64>(Cow::Borrowed(&[
            Operation::Push(Value::Integer(1)),
            Operation::Push(Value::Integer(2)),
            Operation::Add,
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
    let fib = Function {
        arg_count: 1,
        variable_count: 0,
        ops: vec![
            Operation::PushArg(0),
            Operation::If { false_jump_to: 12 },
            Operation::Push(Value::Integer(1)),
            Operation::Push(Value::Integer(2)),
            Operation::Add,
            Operation::Push(Value::Integer(3)),
            Operation::Add,
            Operation::Push(Value::Integer(4)),
            Operation::Add,
            Operation::Push(Value::Integer(5)),
            Operation::Add,
            Operation::Return,
            // If we were passed false, call ourself twice.
            Operation::Push(Value::Boolean(true)),
            Operation::Call {
                vtable_index: None,
                arg_count: 1,
            },
            Operation::Push(Value::Boolean(true)),
            Operation::Call {
                vtable_index: None,
                arg_count: 1,
            },
            Operation::Add, // should produce 30
        ],
    };
    let mut context = Context::new(Budgeted::new(0)).with_function("test", fib);
    let mut fault = context
        .run::<i64>(Cow::Borrowed(&[
            Operation::Push(Value::Boolean(false)),
            Operation::Call {
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
