use std::{
    any::{type_name, Any},
    borrow::Cow,
    cmp::Ordering,
    collections::{HashMap, VecDeque},
    fmt::{Debug, Display},
    marker::PhantomData,
    ops::{Bound, Index, IndexMut, RangeBounds},
    sync::Arc,
    vec,
};

use crate::{ast::CompilationError, parser::parse, symbol::Symbol, Error};

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
    /// Pushes a copy of a value to the stack. The value could be from either an
    /// argument or a variable.
    PushCopy(ValueSource),
    /// Pops a value from the stack and drops the value.
    ///
    /// Attempting to pop beyond the baseline of the currently executing set of
    /// instructions will cause a [`FaultKind::StackUnderflow`] to be returned.
    PopAndDrop,
    /// Returns from the current stack frame.
    Return,
    /// Copies the top value from the stack  into the variable index provided.
    ///
    /// Each function is allocated a fixed number of variables which are
    /// accessed using 0-based indexes. Attempting to use a variable index
    /// outside of the range allocated will cause a
    /// [`FaultKind::InvalidVariableIndex`] to be returned.
    CopyToVariable(usize),
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
    /// Calls a function by name on a value.
    CallInstance {
        /// The target of the function call. If None, the value on the stack
        /// prior to the arguments is the target of the call.
        target: Option<ValueSource>,

        /// The name of the function to call.
        name: Symbol,

        /// The number of arguments on the stack that should be used as
        /// arguments to this call.
        arg_count: usize,
    },
}

/// The source of a value.
#[derive(Debug, Copy, Clone)]
pub enum ValueSource {
    /// The value is in an argument at the provided 0-based index.
    Argument(usize),
    /// The value is in a variable at the provided 0-based index.
    Variable(usize),
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
    /// A real number value (64-bit floating point).
    Real(f64),
    /// A boolean representing true or false.
    Boolean(bool),
    /// A type exposed from Rust.
    Dynamic(Dynamic),
    /// A value representing the lack of a value.
    Void,
}

impl Value {
    /// Returns a new value containing the Rust value provided.
    #[must_use]
    pub fn dynamic(value: impl DynamicValue + 'static) -> Self {
        Self::Dynamic(Dynamic::new(value))
    }

    /// Returns a reference to the contained value, if it was one originally
    /// created with [`Value::dynamic()`]. If the value isn't a dynamic value or
    /// `T` is not the correct type, None will be returned.
    #[must_use]
    pub fn as_dynamic<T: DynamicValue>(&self) -> Option<&T> {
        if let Self::Dynamic(value) = self {
            value.0.as_any().downcast_ref::<T>()
        } else {
            None
        }
    }

    /// Returns a mutable reference to the contained value, if it was one
    /// originally created with [`Value::dynamic()`]. If the value isn't a
    /// dynamic value or `T` is not the correct type, None will be returned.
    ///
    /// Because dynamic values are cheaply cloned by wrapping the value in an
    /// [`Arc`], this method will create a copy of the contained value if there
    /// are any other instances that point to the same contained value. If this
    /// is the only instance of this value, a mutable reference to the contained
    /// value will be returned without additional allocations.
    #[must_use]
    pub fn as_dynamic_mut<T: DynamicValue>(&mut self) -> Option<&mut T> {
        if let Self::Dynamic(value) = self {
            value.as_mut().as_any_mut().downcast_mut()
        } else {
            None
        }
    }

    /// Returns the contained value, if it was one originally created with
    /// [`Value::dynamic()`] and `T` is the same type. If the value contains
    /// another type, `Err(self)` will be returned. Otherwise, the original
    /// value will be returned.
    ///
    /// Because dynamic values are cheaply cloned by wrapping the value in an
    /// [`Arc`], this method will return a clone if there are any other
    /// instances that point to the same contained value. If this is the final
    /// instance of this value, the contained value will be returned without
    /// additional allocations.
    pub fn into_dynamic<T: DynamicValue>(self) -> Result<T, Self> {
        // Before we consume the value, verify we have the correct type.
        if self.as_dynamic::<T>().is_some() {
            // We can now destruct self safely without worrying about needing to
            // return an error.
            let value = if let Self::Dynamic(value) = self {
                value
            } else {
                unreachable!()
            };
            match Arc::try_unwrap(value.0) {
                Ok(mut boxed_value) => {
                    let opt_value = boxed_value
                        .as_opt_any_mut()
                        .downcast_mut::<Option<T>>()
                        .expect("type already checked");
                    let mut value = None;
                    std::mem::swap(opt_value, &mut value);
                    Ok(value.expect("value already taken"))
                }
                Err(arc_value) => Ok(arc_value
                    .as_any()
                    .downcast_ref::<T>()
                    .expect("type already checked")
                    .clone()),
            }
        } else {
            Err(self)
        }
    }

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
            Value::Real(value) => value.abs() < f64::EPSILON,
            Value::Boolean(value) => *value,
            Value::Dynamic(value) => value.0.is_truthy(),
            Value::Void => false,
        }
    }

    /// Returns the inverse of [`is_truthy()`](Self::is_truthy)
    #[must_use]
    #[inline]
    pub fn is_falsey(&self) -> bool {
        !self.is_truthy()
    }

    /// Returns the kind of the contained value.
    #[must_use]
    pub fn kind(&self) -> ValueKind {
        match self {
            Value::Integer(_) => ValueKind::Integer,
            Value::Real(_) => ValueKind::Real,
            Value::Boolean(_) => ValueKind::Boolean,
            Value::Dynamic(value) => ValueKind::Dynamic(value.0.kind()),
            Value::Void => ValueKind::Void,
        }
    }
}

impl Eq for Value {}

impl PartialEq for Value {
    // floating point casts are intentional in this code.
    #[allow(clippy::cast_precision_loss)]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Integer(lhs), Self::Integer(rhs)) => lhs == rhs,
            (Self::Real(lhs), Self::Real(rhs)) => real_total_eq(*lhs, *rhs),
            (Self::Integer(lhs), Self::Real(rhs)) => real_total_eq(*lhs as f64, *rhs),
            (Self::Real(lhs), Self::Integer(rhs)) => real_total_eq(*lhs, *rhs as f64),
            (Self::Boolean(lhs), Self::Boolean(rhs)) => lhs == rhs,
            (Self::Void, Self::Void) => true,
            (Self::Dynamic(lhs), Self::Dynamic(rhs)) => lhs
                .0
                .partial_eq(other)
                .or_else(|| rhs.0.partial_eq(self))
                .unwrap_or(false),
            (Self::Dynamic(lhs), _) => lhs.0.partial_eq(other).unwrap_or(false),
            _ => false,
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Integer(value) => Display::fmt(value, f),
            Value::Real(value) => Display::fmt(value, f),
            Value::Boolean(value) => Display::fmt(value, f),
            Value::Dynamic(dynamic) => Display::fmt(dynamic, f),
            Value::Void => f.write_str("Void"),
        }
    }
}

#[inline]
fn real_eq(lhs: f64, rhs: f64) -> bool {
    (lhs - rhs).abs() < f64::EPSILON
}

fn real_total_eq(lhs: f64, rhs: f64) -> bool {
    match (lhs.is_nan(), rhs.is_nan()) {
        // Neither are NaNs
        (false, false) => {
            match (lhs.is_infinite(), rhs.is_infinite()) {
                // Neither are infinite -- perform a fuzzy floating point eq
                // check using EPSILON as the step.
                (false, false) => real_eq(lhs, rhs),
                // Both are infinite, equality is determined by the signs matching.
                (true, true) => lhs.is_sign_positive() == rhs.is_sign_positive(),
                // One is finite, one is infinite, they aren't equal
                _ => false,
            }
        }
        // Both are NaN. They are only equal if the signs are equal.
        (true, true) => lhs.is_sign_positive() == rhs.is_sign_positive(),
        // One is NaN, the other isn't.
        _ => false,
    }
}

/// This function produces an Ordering for floats as follows:
///
/// - -Infinity
/// - negative real numbers
/// - -0.0
/// - +0.0
/// - positive real numbers
/// - Infinity
/// - NaN
fn real_total_cmp(lhs: f64, rhs: f64) -> Ordering {
    match (lhs.is_nan(), rhs.is_nan()) {
        // Neither are NaNs
        (false, false) => {
            let (lhs_is_infinite, rhs_is_infinite) = (lhs.is_infinite(), rhs.is_infinite());
            let (lhs_is_positive, rhs_is_positive) =
                (lhs.is_sign_positive(), rhs.is_sign_positive());

            match (
                lhs_is_infinite,
                rhs_is_infinite,
                lhs_is_positive,
                rhs_is_positive,
            ) {
                (false, false, _, _) => {
                    if real_eq(lhs, rhs) {
                        Ordering::Equal
                    } else if lhs < rhs {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    }
                }
                // Equal if both are infinite and signs are equal
                (true, true, true, true) | (true, true, false, false) => Ordering::Equal,
                // If only one is infinite, its sign controls the sort.
                (false, _, _, true) | (true, _, false, _) => Ordering::Less,
                (false, _, _, false) | (true, _, true, _) => Ordering::Greater,
            }
        }
        // Both are NaN.
        (true, true) => Ordering::Equal,
        // One is NaN, the other isn't. Unlike infinity, there is no concept of negative nan.
        (false, _) => Ordering::Less,
        (true, _) => Ordering::Greater,
    }
}

#[test]
fn real_cmp_tests() {
    const EXPECTED_ORDER: [f64; 10] = [
        f64::NEG_INFINITY,
        f64::NEG_INFINITY,
        -1.0,
        -0.0,
        0.0,
        1.0,
        f64::INFINITY,
        f64::INFINITY,
        f64::NAN,
        f64::NAN,
    ];

    // NaN comparisons
    assert_eq!(real_total_cmp(f64::NAN, f64::NAN), Ordering::Equal);
    assert_eq!(real_total_cmp(f64::NAN, -1.), Ordering::Greater);
    assert_eq!(real_total_cmp(f64::NAN, 1.), Ordering::Greater);
    assert_eq!(
        real_total_cmp(f64::NAN, f64::NEG_INFINITY),
        Ordering::Greater
    );
    assert_eq!(real_total_cmp(f64::NAN, f64::INFINITY), Ordering::Greater);

    // NaN comparisons reversed
    assert_eq!(real_total_cmp(-1., f64::NAN), Ordering::Less);
    assert_eq!(real_total_cmp(1., f64::NAN,), Ordering::Less);
    assert_eq!(real_total_cmp(f64::NEG_INFINITY, f64::NAN), Ordering::Less);
    assert_eq!(real_total_cmp(f64::INFINITY, f64::NAN), Ordering::Less);

    // Infinity comparisons
    assert_eq!(
        real_total_cmp(f64::INFINITY, f64::INFINITY),
        Ordering::Equal
    );
    assert_eq!(
        real_total_cmp(f64::INFINITY, f64::NEG_INFINITY),
        Ordering::Greater
    );
    assert_eq!(real_total_cmp(f64::INFINITY, -1.), Ordering::Greater);
    assert_eq!(real_total_cmp(f64::INFINITY, 1.), Ordering::Greater);

    // Infinity comparisons reversed
    assert_eq!(
        real_total_cmp(f64::NEG_INFINITY, f64::INFINITY),
        Ordering::Less
    );
    assert_eq!(real_total_cmp(-1., f64::INFINITY,), Ordering::Less);
    assert_eq!(real_total_cmp(1., f64::INFINITY,), Ordering::Less);

    // Negative-Infinity comparisons
    assert_eq!(
        real_total_cmp(f64::NEG_INFINITY, f64::NEG_INFINITY),
        Ordering::Equal
    );
    assert_eq!(real_total_cmp(f64::NEG_INFINITY, -1.), Ordering::Less);
    assert_eq!(real_total_cmp(f64::NEG_INFINITY, 1.), Ordering::Less);

    // Negative-Infinity comparisons reversed
    assert_eq!(real_total_cmp(f64::NEG_INFINITY, -1.), Ordering::Less);
    assert_eq!(real_total_cmp(f64::NEG_INFINITY, 1.), Ordering::Less);
    let mut values = vec![
        1.0,
        f64::INFINITY,
        0.0,
        f64::NEG_INFINITY,
        -1.0,
        -0.0,
        f64::NAN,
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
    ];
    values.sort_by(|a, b| real_total_cmp(*a, *b));
    println!("Sorted: {values:?}");
    for (a, b) in values.iter().zip(EXPECTED_ORDER.iter()) {
        assert!(real_total_eq(*a, *b), "{a} != {b}");
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

impl PartialEq<f64> for Value {
    // floating point casts are intentional in this code.
    #[allow(clippy::cast_precision_loss)]
    fn eq(&self, rhs: &f64) -> bool {
        match self {
            Value::Integer(lhs) => real_total_eq(*lhs as f64, *rhs),
            Value::Real(lhs) => real_total_eq(*lhs, *rhs),
            _ => false,
        }
    }
}

fn dynamic_ord(
    left: &Value,
    left_dynamic: &dyn UnboxableDynamicValue,
    right: &Value,
) -> Option<Ordering> {
    match left_dynamic.partial_cmp(right) {
        Some(ordering) => Some(ordering),
        None => match right {
            Value::Dynamic(right) => right.0.partial_cmp(left).map(Ordering::reverse),
            _ => None,
        },
    }
}

impl PartialOrd for Value {
    #[inline]
    fn partial_cmp(&self, right: &Self) -> Option<Ordering> {
        match self {
            Value::Integer(left) => match right {
                Value::Integer(right) => Some(left.cmp(right)),
                Value::Dynamic(right_dynamic) => {
                    dynamic_ord(right, right_dynamic.0.as_ref().as_ref(), self)
                        .map(Ordering::reverse)
                }
                _ => None,
            },
            Value::Real(left) => match right {
                Value::Real(right) => Some(real_total_cmp(*left, *right)),
                Value::Dynamic(right_dynamic) => {
                    dynamic_ord(right, right_dynamic.0.as_ref().as_ref(), self)
                        .map(Ordering::reverse)
                }
                _ => None,
            },
            Value::Boolean(left) => match right {
                Value::Boolean(right) => Some(left.cmp(right)),
                Value::Dynamic(right_dynamic) => {
                    dynamic_ord(right, right_dynamic.0.as_ref().as_ref(), self)
                        .map(Ordering::reverse)
                }
                _ => None,
            },
            Value::Dynamic(left_dynamic) => {
                dynamic_ord(self, left_dynamic.0.as_ref().as_ref(), right)
            }
            Value::Void => {
                if let Value::Void = right {
                    Some(Ordering::Equal)
                } else {
                    None
                }
            }
        }
    }
}

/// All primitive [`Value`] kinds.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ValueKind {
    /// A signed 64-bit integer value.
    Integer,
    /// A real number value (64-bit floating point).
    Real,
    /// A boolean representing true or false.
    Boolean,
    /// A dynamically exposed Rust type.
    Dynamic(&'static str),
    /// A value representing the lack of a value.
    Void,
}

impl ValueKind {
    /// Returns this kind as a string.
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            ValueKind::Integer => "Integer",
            ValueKind::Real => "Real",
            ValueKind::Boolean => "Boolean",
            ValueKind::Void => "Void",
            ValueKind::Dynamic(name) => name,
        }
    }
}

/// A type that can be used in the virtual machine using [`Value::dynamic`].
pub trait DynamicValue: Clone + Debug + Display + 'static {
    /// Returns true if the value contained is truthy. See
    /// [`Value::is_truthy()`] for examples of what this means for primitive
    /// types.
    fn is_truthy(&self) -> bool;

    /// Returns a unique string identifying this type. This returned string will
    /// be wrapped in [`ValueKind::Dynamic`] when [`Value::kind()`] is invoked
    /// on a dynamic value.
    ///
    /// This value does not influence the virtual machine's behavior. The
    /// virtual machine uses this string only when creating error messages.
    fn kind(&self) -> &'static str;

    /// Returns true if self and other are considered equal. Returns false if
    /// self and other are able to be compared but are not equal. Returns None
    /// if the values are unable to be compared.
    ///
    /// When evaluating `left = right` with dynamic values, if
    /// `left.partial_eq(right)` returns None, `right.partial_eq(left)` will be
    /// attempted before returning false.
    #[allow(unused_variables)]
    fn partial_eq(&self, other: &Value) -> Option<bool> {
        None
    }

    /// Returns the relative ordering of `self` and `other`, if a comparison is
    /// able to be made. If the types cannot be compared, this function should
    /// return None.
    ///
    /// When evaluating a comparison such as `left < right` with dynamic values,
    /// if `left.partial_cmp(right)` returns None,
    /// `right.partial_cmp(left).map(Ordering::reverse)` will be attempted
    /// before returning false.
    #[allow(unused_variables)]
    fn partial_cmp(&self, other: &Value) -> Option<Ordering> {
        None
    }

    /// Calls a function by `name` with `args`.
    #[allow(unused_variables)]
    fn call(&mut self, name: &Symbol, args: vec::Drain<'_, Value>) -> Result<Value, FaultKind> {
        Err(FaultKind::UnknownFunction {
            kind: ValueKind::Dynamic(self.kind()),
            name: name.clone(),
        })
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
    stack: Stack,
    local_module: Module,
    environment: Env,
}

impl Bud<()> {
    /// Returns a default instance of Bud with no custom [`Environment`]
    #[must_use]
    pub fn empty() -> Self {
        Self::default_for(())
    }
}

impl<Env> Bud<Env>
where
    Env: Environment,
{
    /// Returns a new instance with the provided environment.
    pub fn new(
        environment: Env,
        initial_stack_capacity: usize,
        maximum_stack_capacity: usize,
    ) -> Self {
        Self {
            environment,
            stack: Stack::new(initial_stack_capacity, maximum_stack_capacity),
            local_module: Module::default(),
        }
    }

    /// Returns a new instance with the provided environment.
    pub fn default_for(environment: Env) -> Self {
        Self::new(environment, 0, usize::MAX)
    }

    /// Returns a reference to the environment for this instance.
    pub fn environment(&self) -> &Env {
        &self.environment
    }

    /// Returns a mutable refernce to the environment for this instance.
    pub fn environment_mut(&mut self) -> &mut Env {
        &mut self.environment
    }

    /// Returns the stack of this virtual machine.
    #[must_use]
    pub const fn stack(&self) -> &Stack {
        &self.stack
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
    pub fn call<'a, Output: FromStack, Args, ArgsIter>(
        &'a mut self,
        function: &Symbol,
        arguments: Args,
    ) -> Result<Output, Error<'_, Env, Output>>
    where
        Args: IntoIterator<Item = Value, IntoIter = ArgsIter>,
        ArgsIter: Iterator<Item = Value> + ExactSizeIterator + DoubleEndedIterator,
    {
        match self.local_module.contents.get(function) {
            Some(ModuleItem::Function(vtable_index)) => {
                let arg_count = self.stack.extend(arguments)?;
                // TODO It'd be nice to not have to have an allocation here
                self.run(Cow::Owned(vec![Instruction::Call {
                    vtable_index: Some(*vtable_index),
                    arg_count,
                }]))
                .map_err(Error::from)
            }
            None => Err(Error::from(CompilationError::UndefinedFunction(
                function.clone(),
            ))),
        }
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
                kind: FaultOrPause::Pause(paused_evaluation),
                stack,
            }) => {
                let paused_evaluation = PausedExecution {
                    context: Some(self),
                    operations: Some(operations),
                    stack: paused_evaluation.stack,
                    _return: PhantomData,
                };
                return Err(Fault {
                    kind: FaultOrPause::Pause(paused_evaluation),
                    stack,
                });
            }
            other => other?,
        }
        Output::from_stack(self).map_err(Fault::from)
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
                kind: FaultOrPause::Pause(paused_evaluation),
                stack,
            }) => {
                let paused_evaluation = PausedExecution {
                    context: Some(self),
                    operations: Some(operations),
                    stack: paused_evaluation.stack,
                    _return: PhantomData,
                };
                return Err(Fault {
                    kind: FaultOrPause::Pause(paused_evaluation),
                    stack,
                });
            }
            Err(other) => return Err(other),
        }
        Output::from_stack(self).map_err(Fault::from)
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
    stack: &'a mut Stack,
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
        if let Some(call_to_resume) = resume_from.pop_front() {
            // We were calling a function when this happened. We need to finish the call.
            let vtable_index = call_to_resume
                .vtable_index
                .expect("can only resume a called function");
            let function = &self.module.vtable[vtable_index]; // TODO this module isn't necessarily right, but we don't really support modules.
            let mut running_frame = StackFrame {
                module: self.module,
                stack: self.stack,
                environment: self.environment,
                return_offset: call_to_resume.return_offset,
                variables_offset: call_to_resume.variables_offset,
                arg_offset: call_to_resume.arg_offset,
                vtable_index: call_to_resume.vtable_index,
                operation_index: call_to_resume.operation_index,
                _output: PhantomData,
            };
            match running_frame.resume_executing_execute_operations(&function.code, resume_from) {
                Ok(_) => {}
                Err(Fault {
                    kind: FaultOrPause::Pause(mut paused),
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
                        kind: FaultOrPause::Pause(paused),
                        stack,
                    });
                }
                Err(err) => return Err(err),
            };

            self.clean_stack_after_call(call_to_resume.arg_offset, call_to_resume.return_offset)?;

            // The call that was executing when we paused has finished, we can
            // now resume executing our frame's instructions.
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
                    kind: FaultOrPause::Pause(PausedExecution {
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
                    if let FaultOrPause::Pause(paused_frame) = &mut fault.kind {
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
        operation: &Instruction,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        match operation {
            Instruction::JumpTo(instruction_index) => {
                Ok(Some(FlowControl::JumpTo(*instruction_index)))
            }
            Instruction::Add => self.add(),
            Instruction::Sub => self.sub(),
            Instruction::Multiply => self.multiply(),
            Instruction::Divide => self.divide(),
            Instruction::If { false_jump_to } => self.r#if(*false_jump_to),
            Instruction::Compare(comparison) => self.compare(*comparison),
            Instruction::Push(value) => {
                self.stack.push(value.clone())?;
                Ok(None)
            }
            Instruction::PushCopy(ValueSource::Variable(variable)) => self.push_var(*variable),
            Instruction::PushCopy(ValueSource::Argument(arg_index)) => self.push_arg(*arg_index),
            Instruction::PopAndDrop => {
                self.pop()?;
                Ok(None)
            }
            Instruction::Return => Ok(Some(FlowControl::Return)),
            Instruction::CopyToVariable(variable) => self.copy_to_var(*variable),
            Instruction::Call {
                vtable_index,
                arg_count,
            } => self.call(*vtable_index, *arg_count),
            Instruction::CallInstance {
                target,
                name,
                arg_count,
            } => self.call_instance(*target, name, *arg_count),
        }
    }

    fn clean_stack_after_call(
        &mut self,
        arg_offset: usize,
        return_offset: usize,
    ) -> Result<(), Fault<'static, Env, Output>> {
        if arg_offset < return_offset {
            // Remove the args, which sit between the stack and the return value
            self.stack.remove_range(arg_offset..return_offset);
        }

        match self.stack.len() {
            len if len == arg_offset => {
                // The function didn't push a value before returning.
                self.stack.push(Value::Void)?;
            }
            len if len > arg_offset + 1 => {
                // The function more than one value, truncate the stack to the first value popped.
                self.stack.remove_range(arg_offset + 1..);
            }
            _ => {}
        }
        Ok(())
    }

    #[inline]
    fn pop(&mut self) -> Result<Value, FaultKind> {
        if self.stack.len() > self.return_offset {
            self.stack.pop()
        } else {
            Err(FaultKind::StackUnderflow)
        }
    }

    #[inline]
    fn pop_and_modify(&mut self) -> Result<(Value, &mut Value), FaultKind> {
        if self.stack.len() + 1 > self.return_offset {
            self.stack.pop_and_modify()
        } else {
            Err(FaultKind::StackUnderflow)
        }
    }

    // floating point casts are intentional in this code.
    #[allow(clippy::cast_precision_loss)]
    fn add(&mut self) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let (left, right) = self.pop_and_modify()?;
        *right = match (left, &*right) {
            (Value::Integer(left), Value::Integer(right)) => {
                left.checked_add(*right).map_or(Value::Void, Value::Integer)
            }
            (Value::Real(left), Value::Real(right)) => Value::Real(left + *right),
            (Value::Real(left), Value::Integer(right)) => Value::Real(left + *right as f64),
            (Value::Integer(left), Value::Real(right)) => Value::Real(left as f64 + *right),
            (Value::Real(_), other) => {
                return Err(Fault::type_mismatch(
                    "can't add @expected and `@received-value` (@received-type)",
                    ValueKind::Real,
                    other.clone(),
                ))
            }
            (Value::Integer(_), other) => {
                return Err(Fault::type_mismatch(
                    "can't add @expected and `@received-value` (@received-type)",
                    ValueKind::Integer,
                    other.clone(),
                ))
            }
            (other, _) => {
                return Err(Fault::invalid_type(
                    "`@received-value` (@received-type) is not able to be added",
                    other,
                ))
            }
        };
        Ok(None)
    }

    // floating point casts are intentional in this code.
    #[allow(clippy::cast_precision_loss)]
    fn sub(&mut self) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let (left, right) = self.pop_and_modify()?;
        *right = match (left, &*right) {
            (Value::Integer(left), Value::Integer(right)) => {
                left.checked_sub(*right).map_or(Value::Void, Value::Integer)
            }
            (Value::Real(left), Value::Real(right)) => Value::Real(left - *right),
            (Value::Real(left), Value::Integer(right)) => Value::Real(left - *right as f64),
            (Value::Integer(left), Value::Real(right)) => Value::Real(left as f64 - *right),
            (Value::Real(_), other) => {
                return Err(Fault::type_mismatch(
                    "can't subtract @expected and `@received-value` (@received-type)",
                    ValueKind::Real,
                    other.clone(),
                ))
            }
            (Value::Integer(_), other) => {
                return Err(Fault::type_mismatch(
                    "can't subtract @expected and `@received-value` (@received-type)",
                    ValueKind::Integer,
                    other.clone(),
                ))
            }
            (other, _) => {
                return Err(Fault::invalid_type(
                    "`@received-value` (@received-type) is not able to be subtracted",
                    other,
                ))
            }
        };
        Ok(None)
    }

    // floating point casts are intentional in this code.
    #[allow(clippy::cast_precision_loss)]
    fn multiply(&mut self) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let (left, right) = self.pop_and_modify()?;
        *right = match (left, &*right) {
            (Value::Integer(left), Value::Integer(right)) => {
                left.checked_mul(*right).map_or(Value::Void, Value::Integer)
            }
            (Value::Real(left), Value::Real(right)) => Value::Real(left * *right),
            (Value::Real(left), Value::Integer(right)) => Value::Real(left * *right as f64),
            (Value::Integer(left), Value::Real(right)) => Value::Real(left as f64 * *right),
            (Value::Real(_), other) => {
                return Err(Fault::type_mismatch(
                    "can't multiply @expected and `@received-value` (@received-type)",
                    ValueKind::Real,
                    other.clone(),
                ))
            }
            (Value::Integer(_), other) => {
                return Err(Fault::type_mismatch(
                    "can't multiply @expected and `@received-value` (@received-type)",
                    ValueKind::Integer,
                    other.clone(),
                ))
            }
            (other, _) => {
                return Err(Fault::invalid_type(
                    "`@received-value` (@received-type) is not able to be multiplied",
                    other,
                ))
            }
        };
        Ok(None)
    }

    // floating point casts are intentional in this code.
    #[allow(clippy::cast_precision_loss)]
    fn divide(&mut self) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let (left, right) = self.pop_and_modify()?;
        *right = match (left, &*right) {
            (Value::Integer(left), Value::Integer(right)) => {
                left.checked_div(*right).map_or(Value::Void, Value::Integer)
            }
            (Value::Real(left), Value::Real(right)) => Value::Real(left / *right),
            (Value::Real(left), Value::Integer(right)) => Value::Real(left / *right as f64),
            (Value::Integer(left), Value::Real(right)) => Value::Real(left as f64 / *right),
            (Value::Real(_), other) => {
                return Err(Fault::type_mismatch(
                    "can't divide @expected and `@received-value` (@received-type)",
                    ValueKind::Real,
                    other.clone(),
                ))
            }
            (Value::Integer(_), other) => {
                return Err(Fault::type_mismatch(
                    "can't divide @expected and `@received-value` (@received-type)",
                    ValueKind::Integer,
                    other.clone(),
                ))
            }
            (other, _) => {
                return Err(Fault::invalid_type(
                    "`@received-value` (@received-type) is not able to be divided",
                    other,
                ))
            }
        };
        Ok(None)
    }

    fn r#if(
        &mut self,
        false_jump_to: usize,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let value_to_check = self.pop()?;
        if value_to_check.is_truthy() {
            Ok(None)
        } else {
            Ok(Some(FlowControl::JumpTo(false_jump_to)))
        }
    }

    #[allow(clippy::unnecessary_wraps)] // makes caller more clean
    fn equality<const INVERSE: bool>(
        left: &Value,
        right: &mut Value,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let mut result = left.eq(right);
        if INVERSE {
            result = !result;
        }
        *right = Value::Boolean(result);

        Ok(None)
    }

    fn compare_values(
        left: &Value,
        right: &mut Value,
        matcher: impl FnOnce(Ordering) -> bool,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        if let Some(ordering) = left.partial_cmp(right) {
            *right = Value::Boolean(matcher(ordering));
            Ok(None)
        } else {
            let mut received = Value::Void;
            std::mem::swap(&mut received, right);
            Err(Fault::type_mismatch(
                "invalid comparison between @expected and `@received-value` (@received-type)",
                left.kind(),
                received,
            ))
        }
    }

    fn compare(
        &mut self,
        comparison: Comparison,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let (left, right) = self.pop_and_modify()?;
        match comparison {
            Comparison::Equal => Self::equality::<false>(&left, right),
            Comparison::NotEqual => Self::equality::<true>(&left, right),
            Comparison::LessThan => {
                Self::compare_values(&left, right, |ordering| ordering == Ordering::Less)
            }
            Comparison::LessThanOrEqual => Self::compare_values(&left, right, |ordering| {
                matches!(ordering, Ordering::Less | Ordering::Equal)
            }),
            Comparison::GreaterThan => {
                Self::compare_values(&left, right, |ordering| ordering == Ordering::Greater)
            }
            Comparison::GreaterThanOrEqual => Self::compare_values(&left, right, |ordering| {
                matches!(ordering, Ordering::Greater | Ordering::Equal)
            }),
        }
    }

    fn push_var(
        &mut self,
        variable: usize,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        if let Some(stack_offset) = self.variables_offset.checked_add(variable) {
            if stack_offset < self.return_offset {
                let value = self.stack[stack_offset].clone();
                self.stack.push(value)?;
                return Ok(None);
            }
        }
        Err(Fault::from(FaultKind::InvalidVariableIndex))
    }

    fn push_arg(&mut self, arg: usize) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        if let Some(stack_offset) = self.arg_offset.checked_add(arg) {
            if stack_offset < self.variables_offset {
                let value = self.stack[stack_offset].clone();
                self.stack.push(value)?;
                return Ok(None);
            }
        }
        Err(Fault::from(FaultKind::InvalidArgumentIndex))
    }

    fn copy_to_var(
        &mut self,
        variable: usize,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        if self.stack.len() >= self.return_offset {
            let value = self.stack.top()?;
            if let Some(stack_offset) = self.variables_offset.checked_add(variable) {
                if stack_offset < self.return_offset {
                    self.stack[stack_offset] = value.clone();
                }
            }
            Ok(None)
        } else {
            Err(Fault::stack_underflow())
        }
    }

    fn call(
        &mut self,
        vtable_index: Option<usize>,
        arg_count: usize,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let vtable_index = vtable_index
            .or(self.vtable_index)
            .ok_or(FaultKind::InvalidVtableIndex)?;
        let function = &self
            .module
            .vtable
            .get(vtable_index)
            .ok_or(FaultKind::InvalidVtableIndex)?;

        assert_eq!(function.arg_count, arg_count);

        let variables_offset = self.stack.len();
        let return_offset = variables_offset + function.variable_count;
        let arg_offset = variables_offset - function.arg_count;
        if function.variable_count > 0 {
            self.stack.grow_to(return_offset)?;
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

        self.clean_stack_after_call(arg_offset, return_offset)?;

        Ok(None)
    }

    fn call_instance(
        &mut self,
        target: Option<ValueSource>,
        name: &Symbol,
        arg_count: usize,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        // To prevent overlapping a mutable borrow of the value plus immutable
        // borrows of the stack, we temporarily take the value from where it
        // lives.
        let stack_index = match target {
            Some(ValueSource::Argument(index)) => {
                if let Some(stack_index) = self.arg_offset.checked_add(index) {
                    if stack_index < self.variables_offset {
                        stack_index
                    } else {
                        return Err(Fault::from(FaultKind::InvalidArgumentIndex));
                    }
                } else {
                    return Err(Fault::from(FaultKind::InvalidArgumentIndex));
                }
            }
            Some(ValueSource::Variable(index)) => {
                if let Some(stack_index) = self.variables_offset.checked_add(index) {
                    if stack_index < self.return_offset {
                        stack_index
                    } else {
                        return Err(Fault::from(FaultKind::InvalidVariableIndex));
                    }
                } else {
                    return Err(Fault::from(FaultKind::InvalidVariableIndex));
                }
            }
            None => {
                // If None, the target is the value prior to the arguments.
                if let Some(stack_index) = self
                    .stack
                    .len()
                    .checked_sub(arg_count)
                    .and_then(|index| index.checked_sub(1))
                {
                    if stack_index >= self.return_offset {
                        stack_index
                    } else {
                        return Err(Fault::stack_underflow());
                    }
                } else {
                    return Err(Fault::stack_underflow());
                }
            }
        };

        let return_offset = self.stack.len();
        let arg_offset = return_offset.checked_sub(arg_count);
        let arg_offset = match arg_offset {
            Some(arg_offset) if arg_offset >= self.return_offset => arg_offset,
            _ => return Err(Fault::stack_underflow()),
        };

        // Pull the target out of its current location.
        let mut target_value = Value::Void;
        std::mem::swap(&mut target_value, &mut self.stack[stack_index]);
        // Call without resolving any errors
        let result = match &mut target_value {
            Value::Dynamic(value) => value.call(name, self.stack.drain(arg_offset..return_offset)),

            _ => {
                return Err(Fault::from(FaultKind::invalid_type(
                    "@received-kind does not support function calls",
                    target_value,
                )))
            }
        };
        if target.is_some() {
            // Return the target to its proper location
            std::mem::swap(&mut target_value, &mut self.stack[stack_index]);
        } else {
            // Remove the target's stack space. We didn't do this earlier
            // because it would have caused a copy of all args. But at this
            // point, all the args have been drained during the call so the
            // target can simply be popped.
            self.stack.pop()?;
        }

        // If there was a fault, return.
        let produced_value = result?;
        self.stack.push(produced_value)?;

        Ok(None)
    }
}

/// An unexpected event occurred while executing the virtual machine.
#[derive(Debug)]
pub struct Fault<'a, Env, ReturnType> {
    /// The kind of fault this is.
    pub kind: FaultOrPause<'a, Env, ReturnType>,
    /// The stack trace of the virtual machine when the fault was raised.
    pub stack: Vec<FaultStackFrame>,
}

impl<'a, Env, ReturnType> Fault<'a, Env, ReturnType> {
    fn stack_underflow() -> Self {
        Self::from(FaultKind::StackUnderflow)
    }

    fn invalid_type(message: impl Into<String>, received: Value) -> Self {
        Self::from(FaultKind::invalid_type(message, received))
    }

    fn type_mismatch(message: impl Into<String>, expected: ValueKind, received: Value) -> Self {
        Self::from(FaultKind::type_mismatch(message, expected, received))
    }
}

impl<'a, Env, ReturnType> From<FaultKind> for Fault<'a, Env, ReturnType> {
    fn from(kind: FaultKind) -> Self {
        Self {
            kind: FaultOrPause::Fault(kind),
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
        match &self.kind {
            FaultOrPause::Fault(fault) => Display::fmt(fault, f),
            FaultOrPause::Pause(_) => f.write_str("paused execution"),
        }
    }
}

/// A reason for a virtual machine [`Fault`].
#[derive(Debug)]
pub enum FaultOrPause<'a, Env, ReturnType> {
    /// A fault occurred while processing instructions.
    Fault(FaultKind),
    /// Execution was paused by the [`Environment`] as a result of returning
    /// [`ExecutionBehavior::Pause`] from [`Environment::step`].
    ///
    /// The contained [`PausedExecution`] can be used to resume executing the
    /// code.
    Pause(PausedExecution<'a, Env, ReturnType>),
}

/// An unexpected event within the virtual machine.
#[derive(Debug)]
pub enum FaultKind {
    /// An attempt to push a value to the stack was made after the stack has
    /// reached its capacity.
    StackOverflow,
    /// An attempt to pop a value off of the stack was made when no values were
    /// present in the current code's stack frame.
    StackUnderflow,
    /// An invalid variable index was used.
    InvalidVariableIndex,
    /// An invalid argument index was used.
    InvalidArgumentIndex,
    /// An invalid vtable index was used.
    InvalidVtableIndex,
    /// A call was made to a function that does not exist.
    UnknownFunction {
        /// The kind of the value the function was called on.
        kind: ValueKind,
        /// The name of the function being called.
        name: Symbol,
    },
    /// A value type was unexpected in the given context.
    TypeMismatch {
        /// The error message explaining the type mismatch.
        ///
        /// These patterns will be replaced in `message` before being Displayed:
        ///
        /// - @expected
        /// - @received-value
        /// - @received-kind
        message: String,
        /// The kind expected in this context.
        expected: ValueKind,
        /// The value that caused an error.
        received: Value,
    },
    /// An invalid value type was encountered.
    InvalidType {
        /// The error message explaining the type mismatch.
        ///
        /// These patterns will be replaced in `message` before being Displayed:
        ///
        /// - @received-value
        /// - @received-kind
        message: String,
        /// The value that caused an error.
        received: Value,
    },
    /// An error arose from dynamic types.
    Dynamic(DynamicFault),
}

impl FaultKind {
    fn invalid_type(message: impl Into<String>, received: Value) -> Self {
        FaultKind::InvalidType {
            message: message.into(),
            received,
        }
    }

    fn type_mismatch(message: impl Into<String>, expected: ValueKind, received: Value) -> Self {
        FaultKind::TypeMismatch {
            message: message.into(),
            expected,
            received,
        }
    }
}

impl std::error::Error for FaultKind {}

impl Display for FaultKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FaultKind::StackOverflow => f.write_str("stack pushed to while at maximum capacity"),
            FaultKind::StackUnderflow => f.write_str("stack popped but no values present"),
            FaultKind::InvalidVariableIndex => {
                f.write_str("a variable index was outside of the range allocated for the function")
            }
            FaultKind::InvalidArgumentIndex => f.write_str(
                "an argument index was beyond the number of arguments passed to the function",
            ),
            FaultKind::InvalidVtableIndex => f.write_str(
                "a vtable index was beyond the number functions registerd in the current module",
            ),
            FaultKind::UnknownFunction { kind, name } => {
                write!(f, "unknown function {name} on {}", kind.as_str())
            }
            FaultKind::TypeMismatch {
                message,
                expected,
                received,
            } => {
                let message = message.replace("@expected", expected.as_str());
                let message = message.replace("@received-type", received.kind().as_str());
                let message = message.replace("@received-value", &received.to_string());
                f.write_str(&message)
            }
            FaultKind::InvalidType { message, received } => {
                let message = message.replace("@received-type", received.kind().as_str());
                let message = message.replace("@received-value", &received.to_string());
                f.write_str(&message)
            }
            FaultKind::Dynamic(dynamic) => dynamic.fmt(f),
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
    fn from_stack<Env>(stack: &mut Bud<Env>) -> Result<Self, FaultKind>;
}

impl FromStack for Value {
    fn from_stack<Env>(stack: &mut Bud<Env>) -> Result<Self, FaultKind> {
        stack.stack.pop()
    }
}

impl FromStack for i64 {
    fn from_stack<Env>(stack: &mut Bud<Env>) -> Result<Self, FaultKind> {
        match stack.stack.pop()? {
            Value::Integer(integer) => Ok(integer),
            other => Err(FaultKind::type_mismatch(
                "@expected expected but received `@received-value` (@received-type)",
                ValueKind::Integer,
                other,
            )),
        }
    }
}

impl FromStack for f64 {
    fn from_stack<Env>(stack: &mut Bud<Env>) -> Result<Self, FaultKind> {
        match stack.stack.pop()? {
            Value::Real(number) => Ok(number),
            other => Err(FaultKind::type_mismatch(
                "@expected expected but received `@received-value` (@received-type)",
                ValueKind::Real,
                other,
            )),
        }
    }
}

impl FromStack for bool {
    fn from_stack<Env>(stack: &mut Bud<Env>) -> Result<Self, FaultKind> {
        match stack.stack.pop()? {
            Value::Boolean(value) => Ok(value),
            other => Err(FaultKind::type_mismatch(
                "@expected expected but received `@received-value` (@received-type)",
                ValueKind::Boolean,
                other,
            )),
        }
    }
}

impl FromStack for () {
    fn from_stack<Env>(_stack: &mut Bud<Env>) -> Result<Self, FaultKind> {
        Ok(())
    }
}

impl<T> FromStack for T
where
    T: DynamicValue,
{
    fn from_stack<Env>(stack: &mut Bud<Env>) -> Result<Self, FaultKind> {
        stack.stack.pop()?.into_dynamic().map_err(|value| {
            FaultKind::type_mismatch("invalid type", ValueKind::Dynamic(type_name::<T>()), value)
        })
    }
}

/// A Rust value that has been wrapped for use in the virtual machine.
#[derive(Clone, Debug)]
pub struct Dynamic(
    // The reason for `Arc<Box<dyn UnboxableDynamicValue>>` instead of `Arc<dyn
    // UnboxableDynamicValue>` is the size. `Arc<dyn>` uses a fat pointer which
    // results in 16-bytes being used. By boxing the `dyn` value first, the Arc
    // pointer becomes a normal pointer resulting in this type being only 8
    // bytes.
    Arc<Box<dyn UnboxableDynamicValue>>,
);

#[test]
fn sizes() {
    assert_eq!(
        std::mem::size_of::<Dynamic>(),
        std::mem::size_of::<*const u8>()
    );
    assert_eq!(
        std::mem::size_of::<Symbol>(),
        std::mem::size_of::<*const u8>()
    );
    assert_eq!(
        std::mem::size_of::<Value>(),
        std::mem::size_of::<(*const u8, usize)>()
    );
}

impl Dynamic {
    fn new(value: impl DynamicValue + 'static) -> Self {
        Self(Arc::new(Box::new(DynamicValueData(Some(value)))))
    }

    fn as_mut(&mut self) -> &mut Box<dyn UnboxableDynamicValue> {
        if Arc::strong_count(&self.0) > 1 {
            // More than one reference to this Arc, we have to create a
            // clone instead. We do this before due to overlapping lifetime
            // issues using get_mut twice. We can't use make_mut due to
            // Box<dyn> not being cloneable.
            let new_value = self.0.cloned();
            self.0 = Arc::new(new_value);
        }

        Arc::get_mut(&mut self.0).expect("checked strong count") // This will need to change if we ever allow weak references.
    }

    fn call(
        &mut self,
        name: &Symbol,
        arguments: vec::Drain<'_, Value>,
    ) -> Result<Value, FaultKind> {
        self.as_mut().call(name, arguments)
    }
}

impl Display for Dynamic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

trait UnboxableDynamicValue: Debug + Display {
    fn cloned(&self) -> Box<dyn UnboxableDynamicValue>;
    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
    fn as_opt_any_mut(&mut self) -> &mut dyn Any;

    fn is_truthy(&self) -> bool;
    fn kind(&self) -> &'static str;
    fn partial_eq(&self, other: &Value) -> Option<bool>;
    fn partial_cmp(&self, other: &Value) -> Option<Ordering>;
    fn call(&mut self, name: &Symbol, arguments: vec::Drain<'_, Value>)
        -> Result<Value, FaultKind>;
}

#[derive(Clone)]
struct DynamicValueData<T>(Option<T>);

impl<T> DynamicValueData<T> {
    #[inline]
    fn value(&self) -> &T {
        self.0.as_ref().expect("value taken")
    }
    #[inline]
    fn value_mut(&mut self) -> &mut T {
        self.0.as_mut().expect("value taken")
    }
}

impl<T> UnboxableDynamicValue for DynamicValueData<T>
where
    T: DynamicValue + Any + Debug,
{
    fn cloned(&self) -> Box<dyn UnboxableDynamicValue> {
        Box::new(self.clone())
    }

    fn as_any(&self) -> &dyn Any {
        self.value()
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self.value_mut()
    }

    fn as_opt_any_mut(&mut self) -> &mut dyn Any {
        &mut self.0
    }

    fn is_truthy(&self) -> bool {
        self.value().is_truthy()
    }

    fn kind(&self) -> &'static str {
        self.value().kind()
    }

    fn partial_eq(&self, other: &Value) -> Option<bool> {
        self.value().partial_eq(other)
    }

    fn partial_cmp(&self, other: &Value) -> Option<Ordering> {
        self.value().partial_cmp(other)
    }

    fn call(
        &mut self,
        name: &Symbol,
        arguments: vec::Drain<'_, Value>,
    ) -> Result<Value, FaultKind> {
        self.value_mut().call(name, arguments)
    }
}

impl<T> DynamicValue for DynamicValueData<T>
where
    T: DynamicValue,
{
    fn is_truthy(&self) -> bool {
        self.value().is_truthy()
    }

    fn kind(&self) -> &'static str {
        self.value().kind()
    }

    fn partial_eq(&self, other: &Value) -> Option<bool> {
        self.value().partial_eq(other)
    }

    fn partial_cmp(&self, other: &Value) -> Option<Ordering> {
        self.value().partial_cmp(other)
    }
}

impl<T> Debug for DynamicValueData<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(value) = self.0.as_ref() {
            Debug::fmt(value, f)
        } else {
            f.debug_struct("DynamicValueData").finish_non_exhaustive()
        }
    }
}

impl<T> Display for DynamicValueData<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(value) = self.0.as_ref() {
            Display::fmt(value, f)
        } else {
            Ok(())
        }
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
    /// paused and a [`FaultOrPause::Pause`] is raised. If the execution is
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
    let mut context = Bud::default_for(Budgeted::new(0));
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
            FaultOrPause::Pause(pending) => pending,
            FaultOrPause::Fault(error) => unreachable!("unexpected error: {error}"),
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
            Instruction::PushCopy(ValueSource::Argument(0)),
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
    let mut context = Bud::default_for(Budgeted::new(0)).with_function("test", test);
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
            FaultOrPause::Pause(pending) => pending,
            FaultOrPause::Fault(error) => unreachable!("unexpected error: {error}"),
        };
        pending.environment_mut().add_budget(1);

        fault = match pending.resume() {
            Ok(result) => break result,
            Err(err) => err,
        };
    };

    assert_eq!(output, 30);
}

/// A stack of [`Value`]s.
#[derive(Debug)]
pub struct Stack {
    values: Vec<Value>,
    remaining_capacity: usize,
}

impl Default for Stack {
    fn default() -> Self {
        Self {
            values: Vec::default(),
            remaining_capacity: usize::MAX,
        }
    }
}

impl Stack {
    /// Returns a new stack with enough reserved space to store
    /// `initial_capacity` values without reallocating and will not allow
    /// pushing more than `maximum_capacity` values.
    #[must_use]
    pub fn new(initial_capacity: usize, maximum_capacity: usize) -> Self {
        Self {
            values: Vec::with_capacity(initial_capacity),
            remaining_capacity: maximum_capacity,
        }
    }

    /// Pushes `value` to the stack.
    ///
    /// # Errors
    ///
    /// Returns [`FaultKind::StackOverflow`] if the stack's maximum capacity has
    /// been reached.
    #[inline]
    pub fn push(&mut self, value: Value) -> Result<(), FaultKind> {
        if self.remaining_capacity > 0 {
            self.remaining_capacity -= 1;

            self.values.push(value);
            Ok(())
        } else {
            Err(FaultKind::StackOverflow)
        }
    }

    /// Pushes multiple arguments to the stack.
    pub fn extend<Args, ArgsIter>(&mut self, args: Args) -> Result<usize, FaultKind>
    where
        Args: IntoIterator<Item = Value, IntoIter = ArgsIter>,
        ArgsIter: Iterator<Item = Value> + ExactSizeIterator + DoubleEndedIterator,
    {
        let args = args.into_iter();
        let arg_count = args.len();
        if self.remaining_capacity >= arg_count {
            self.remaining_capacity -= arg_count;
            self.values.extend(args.rev());
            Ok(arg_count)
        } else {
            Err(FaultKind::StackOverflow)
        }
    }

    /// Pushes multiple arguments to the stack.
    pub fn drain<Range>(&mut self, range: Range) -> vec::Drain<'_, Value>
    where
        Range: RangeBounds<usize>,
    {
        let start = match range.start_bound() {
            Bound::Included(start) => *start,
            Bound::Excluded(start) => start.saturating_sub(1),
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(end) => end.saturating_add(1),
            Bound::Excluded(end) => *end,
            Bound::Unbounded => self.values.len(),
        };
        let elements_removed = end - start;
        self.remaining_capacity += elements_removed;
        self.values.drain(start..end)
    }

    /// Returns a reference to the top [`Value`] on the stack, or returns a
    /// [`FaultKind::StackUnderflow`] if no values are present.
    #[inline]
    pub fn top(&self) -> Result<&Value, FaultKind> {
        if let Some(value) = self.values.last() {
            Ok(value)
        } else {
            Err(FaultKind::StackUnderflow)
        }
    }

    /// Pops a [`Value`] from the stack.
    ///
    /// # Errors
    ///
    /// Returns [`FaultKind::StackUnderflow`] if the stack is empty.
    #[inline]
    pub fn pop(&mut self) -> Result<Value, FaultKind> {
        if let Some(value) = self.values.pop() {
            self.remaining_capacity += 1;
            Ok(value)
        } else {
            Err(FaultKind::StackUnderflow)
        }
    }

    /// Pops a [`Value`] from the stack and returns a mutable reference to the
    /// next value.
    ///
    /// # Errors
    ///
    /// Returns [`FaultKind::StackUnderflow`] if the stack does not contain at
    /// least two values.
    #[inline]
    pub fn pop_and_modify(&mut self) -> Result<(Value, &mut Value), FaultKind> {
        if self.values.len() >= 2 {
            let first = self.values.pop().expect("bounds already checked");
            self.remaining_capacity += 1;

            Ok((
                first,
                self.values.last_mut().expect("bounds already checked"),
            ))
        } else {
            Err(FaultKind::StackUnderflow)
        }
    }

    /// Returns the number of [`Value`]s contained in this stack.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Returns true if this stack has no values.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of [`Value`]s that can be pushed to this stack before
    /// a [`FaultKind::StackOverflow`] is raised.
    #[must_use]
    pub const fn remaining_capacity(&self) -> usize {
        self.remaining_capacity
    }

    #[inline]
    fn remove_range<R>(&mut self, range: R)
    where
        R: RangeBounds<usize>,
    {
        let removed = self.values.drain(range).count();
        self.remaining_capacity += removed;
    }

    #[inline]
    fn grow_to<Env, ReturnType>(
        &mut self,
        new_size: usize,
    ) -> Result<(), Fault<'static, Env, ReturnType>> {
        let extra_capacity = new_size.saturating_sub(self.len());
        if extra_capacity <= self.remaining_capacity {
            self.values.resize(new_size, Value::Void);
            self.remaining_capacity -= extra_capacity;
            Ok(())
        } else {
            Err(Fault::from(FaultKind::StackOverflow))
        }
    }
}

impl Index<usize> for Stack {
    type Output = Value;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.values[index]
    }
}

impl IndexMut<usize> for Stack {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.values[index]
    }
}

/// A [`Fault`] that arose from a [`Dynamic`] value.
#[derive(Debug)]
pub struct DynamicFault(Box<dyn AnyDynamicError>);

impl DynamicFault {
    /// Returns a new instance containing the provided error.
    pub fn new<T: Debug + Display + 'static>(error: T) -> Self {
        Self(Box::new(DynamicErrorContents(Some(error))))
    }

    /// Returns a reference to the original error, if `T` is the same type that
    /// was provided during construction.
    #[must_use]
    pub fn downcast_ref<T: Debug + Display + 'static>(&self) -> Option<&T> {
        self.0.as_any().downcast_ref()
    }

    /// Returns the original error if `T` is the same type that was provided
    /// during construction. If not, `Err(self)` will be returned.
    pub fn try_unwrap<T: Debug + Display + 'static>(mut self) -> Result<T, Self> {
        if let Some(opt_any) = self.0.as_opt_any_mut().downcast_mut::<Option<T>>() {
            Ok(std::mem::take(opt_any).expect("value already taken"))
        } else {
            Err(self)
        }
    }
}

#[test]
fn dynamic_error_conversions() {
    let error = DynamicFault::new(true);
    assert!(*error.downcast_ref::<bool>().unwrap());
    assert!(error.try_unwrap::<bool>().unwrap());
}

#[derive(Debug)]
struct DynamicErrorContents<T>(Option<T>);

impl<T> Display for DynamicErrorContents<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(value) = self.0.as_ref() {
            Display::fmt(value, f)
        } else {
            Ok(())
        }
    }
}

trait AnyDynamicError: Debug + Display {
    fn as_any(&self) -> &dyn Any;
    fn as_opt_any_mut(&mut self) -> &mut dyn Any;
}

impl<T> AnyDynamicError for DynamicErrorContents<T>
where
    T: Debug + Display + 'static,
{
    fn as_any(&self) -> &dyn Any {
        self.0.as_ref().expect("value taken")
    }

    fn as_opt_any_mut(&mut self) -> &mut dyn Any {
        &mut self.0
    }
}

#[test]
fn invalid_variables() {
    let test = Function {
        arg_count: 0,
        variable_count: 0,
        code: vec![Instruction::PushCopy(ValueSource::Variable(0))],
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
        FaultOrPause::Fault(FaultKind::InvalidVariableIndex)
    ));
}

#[test]
fn invalid_argument() {
    let test = Function {
        arg_count: 0,
        variable_count: 0,
        code: vec![Instruction::PushCopy(ValueSource::Argument(0))],
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
        FaultOrPause::Fault(FaultKind::InvalidArgumentIndex)
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
        FaultOrPause::Fault(FaultKind::InvalidVtableIndex)
    ));
}

#[test]
fn function_without_return_value() {
    let test = Function {
        arg_count: 0,
        variable_count: 0,
        code: vec![],
    };
    let mut context = Bud::empty().with_function("test", test);
    assert_eq!(
        context
            .call::<Value, _, _>(&Symbol::from("test"), [])
            .unwrap(),
        Value::Void
    );
}

#[test]
fn function_needs_extra_cleanup() {
    let test = Function {
        arg_count: 0,
        variable_count: 0,
        code: vec![
            Instruction::Push(Value::Integer(1)),
            Instruction::Push(Value::Integer(2)),
        ],
    };
    let mut context = Bud::empty().with_function("test", test);
    assert_eq!(
        context
            .run::<Value>(Cow::Borrowed(&[Instruction::Call {
                vtable_index: Some(0),
                arg_count: 0,
            }]))
            .unwrap(),
        Value::Integer(1)
    );

    assert!(context.stack().is_empty());
}
