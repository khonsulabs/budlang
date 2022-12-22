#![doc = include_str!(".crate-docs.md")]
#![forbid(unsafe_code)]
#![warn(
    clippy::cargo,
    missing_docs,
    clippy::pedantic,
    future_incompatible,
    rust_2018_idioms
)]
#![allow(
    clippy::option_if_let_else,
    clippy::module_name_repetitions,
    clippy::missing_errors_doc
)]

use std::{
    any::{type_name, Any},
    borrow::Cow,
    cmp::Ordering,
    collections::{HashMap as StdHashMap, VecDeque},
    fmt::{Debug, Display, Write},
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::{Add, Bound, Div, Index, IndexMut, Mul, RangeBounds, Sub},
    str::FromStr,
    sync::Arc,
    vec,
};

/// A `HashMap` implementation that provides a defined iteration order.
pub mod budmap;
mod dynamic;
pub mod ir;
pub mod lexer_util;
mod list;
mod map;
mod string;
mod symbol;

use crate::ir::{Scope, ScopeSymbolKind};

pub use self::{
    dynamic::{Dynamic, DynamicValue},
    list::List,
    map::HashMap,
    string::StringLiteralDisplay,
    symbol::Symbol,
};

/// A virtual machine instruction.
///
/// This enum contains all instructions that the virtual machine is able to
/// perform.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Instruction<Intrinsic> {
    /// Adds `left` and `right` and places the result in `destination`.
    ///
    /// If this operation causes an overflow, [`Value::Void`] will be stored in
    /// the destination instead.
    Add {
        /// The left hand side of the operation.
        left: ValueOrSource,
        /// The right hand side of the operation.
        right: ValueOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Subtracts `right` from `left` and places the result in `destination`.
    ///
    /// If this operation causes an overflow, [`Value::Void`] will be stored in
    /// the destination instead.
    Sub {
        /// The left hand side of the operation.
        left: ValueOrSource,
        /// The right hand side of the operation.
        right: ValueOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Multiply `left` by `right` and places the result in `destination`.
    ///
    /// If this operation causes an overflow, [`Value::Void`] will be stored in
    /// the destination instead.
    Multiply {
        /// The left hand side of the operation.
        left: ValueOrSource,
        /// The right hand side of the operation.
        right: ValueOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Divides `left` by `right` and places the result in `destination`.
    ///
    /// If this operation causes an overflow, [`Value::Void`] will be stored in
    /// the destination instead.
    Divide {
        /// The left hand side of the operation.
        left: ValueOrSource,
        /// The right hand side of the operation.
        right: ValueOrSource,
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
        left: ValueOrSource,
        /// The right hand side of the operation.
        right: ValueOrSource,
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
        left: ValueOrSource,
        /// The right hand side of the operation.
        right: ValueOrSource,
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
        left: ValueOrSource,
        /// The right hand side of the operation.
        right: ValueOrSource,
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
        left: ValueOrSource,
        /// The right hand side of the operation.
        right: ValueOrSource,
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
        left: ValueOrSource,
        /// The right hand side of the operation.
        right: ValueOrSource,
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
        left: ValueOrSource,
        /// The right hand side of the operation.
        right: ValueOrSource,
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
        left: ValueOrSource,
        /// The number of bits to shift by
        right: ValueOrSource,
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
        left: ValueOrSource,
        /// The number of bits to shift by
        right: ValueOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Performs a logical `not` operation for `value`, storing the result in
    /// `destination`.
    ///
    /// If the value is truthy, false will be stored in the destination. If the
    /// value is falsey, true will be stored in the destination.
    LogicalNot {
        /// The left hand side of the operation.
        value: ValueOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Performs a bitwise not operation for `value`, storing the result in
    /// `destination`. This operation always results in a [`Value::Integer`].
    ///
    /// If `value` cannot be coerced to an integer, a fault will be returned.
    ///
    /// The result will be `value` with each bit flipped.
    BitwiseNot {
        /// The left hand side of the operation.
        value: ValueOrSource,
        /// The destination for the result to be stored in.
        destination: Destination,
    },
    /// Converts a value to another type, storing the result in `destination`.
    ///
    /// If `value` cannot be converted, a fault will be returned.
    Convert {
        /// The left hand side of the operation.
        value: ValueOrSource,
        /// The type to convert to.
        kind: ValueKind,
        /// The destination for the converted value to be stored in.
        destination: Destination,
    },
    /// Checks [`condition.is_truthy()`](Value::is_truthy), jumping to the
    /// target instruction if false.
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
        /// The source of the condition.
        condition: ValueOrSource,
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
    /// Compares `left` and `right` using `comparison` to evaluate a boolean
    /// result.
    ///
    /// If [`CompareAction::Store`] is used, the boolean result will
    /// be stored in the provided destination.
    ///
    /// If [`CompareAction::JumpIfFalse`] is used and the result is false,
    /// execution will jump to the 0-based instruction index within the current
    /// set of executing instructions. If the result is true, the next
    /// instruction will continue executing.
    Compare {
        /// The comparison to perform.
        comparison: Comparison,
        /// The left hand side of the operation.
        left: ValueOrSource,
        /// The right hand side of the operation.
        right: ValueOrSource,
        /// The action to take with the result of the comparison.
        action: CompareAction,
    },
    /// Pushes a value to the stack.
    Push(ValueOrSource),
    /// Returns from the current stack frame.
    Return(Option<ValueOrSource>),
    /// Loads a `value` into a variable.
    Load {
        /// The index of the variable to store the value in.
        variable_index: usize,
        /// The value or source of the value to store.
        value: ValueOrSource,
    },
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
        target: Option<ValueOrSource>,

        /// The name of the function to call.
        name: Symbol,

        /// The number of arguments on the stack that should be used as
        /// arguments to this call.
        arg_count: usize,

        /// The destination for the result of the call.
        destination: Destination,
    },
}

impl<Intrinsic> Display for Instruction<Intrinsic>
where
    Intrinsic: Display,
{
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
            Instruction::LogicalNot { value, destination } => {
                write!(f, "not {value} {destination}")
            }
            Instruction::BitwiseNot { value, destination } => {
                write!(f, "bitnot {value} {destination}")
            }
            Instruction::Convert {
                value,
                kind,
                destination,
            } => {
                write!(f, "convert {value} {kind} {destination}")
            }
            Instruction::If {
                condition,
                false_jump_to,
            } => write!(f, "if !{condition} jump {false_jump_to}"),
            Instruction::JumpTo(instruction) => write!(f, "jump {instruction}"),
            Instruction::Compare {
                comparison,
                left,
                right,
                action,
            } => write!(f, "{comparison} {left} {right} {action}"),
            Instruction::Push(value) => write!(f, "push {value}"),
            Instruction::Load {
                value,
                variable_index,
            } => write!(f, "load {value} ${variable_index}"),
            Instruction::Return(opt_value) => {
                if let Some(value) = opt_value {
                    write!(f, "return {value}")
                } else {
                    f.write_str("return")
                }
            }
            Instruction::Call {
                vtable_index,
                arg_count,
                destination,
            } => {
                if let Some(vtable_index) = vtable_index {
                    write!(f, "call #{vtable_index} {arg_count} {destination}")
                } else {
                    write!(f, "recurse {arg_count} {destination}")
                }
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
                    write!(f, "invoke $ {name} {arg_count} {destination}")
                }
            }
            Instruction::CallIntrinsic {
                intrinsic,
                arg_count,
                destination,
            } => {
                write!(f, "intrinsic {intrinsic} {arg_count} {destination}")
            }
        }
    }
}

/// An action to take during an [`Instruction::Compare`].
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum CompareAction {
    /// Store the boolean result in the destination indicated.
    Store(Destination),
    /// If the comparison is false, jump to the 0-based instruction index
    /// indicated.
    JumpIfFalse(usize),
}

impl Display for CompareAction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompareAction::Store(destination) => Display::fmt(destination, f),
            CompareAction::JumpIfFalse(label) => write!(f, "jump {label}"),
        }
    }
}

/// A destination for a value.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Destination {
    /// Store the value in the 0-based variable index provided.
    Variable(usize),
    /// Push the value to the stack.
    Stack,
    /// Store the value in the return register.
    Return,
}

impl Display for Destination {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Destination::Variable(variable) => write!(f, "${variable}"),
            Destination::Stack => f.write_str("$"),
            Destination::Return => f.write_str("$$"),
        }
    }
}

/// The source of a value.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ValueSource {
    /// The value is in an argument at the provided 0-based index.
    Argument(usize),
    /// The value is in a variable at the provided 0-based index.
    Variable(usize),
}

impl Display for ValueSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueSource::Argument(index) => write!(f, "@{index}"),
            ValueSource::Variable(variable) => write!(f, "${variable}"),
        }
    }
}

/// A value or a location of a value
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ValueOrSource {
    /// A value.
    Value(Value),
    /// The value is in an argument at the provided 0-based index.
    Argument(usize),
    /// The value is in a variable at the provided 0-based index.
    Variable(usize),
}

impl Display for ValueOrSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueOrSource::Value(value) => Display::fmt(value, f),
            ValueOrSource::Argument(index) => write!(f, "@{index}"),
            ValueOrSource::Variable(variable) => write!(f, "${variable}"),
        }
    }
}

/// A method for comparing [`Value`]s.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
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

impl Display for Comparison {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Comparison::Equal => f.write_str("eq"),
            Comparison::NotEqual => f.write_str("neq"),
            Comparison::LessThan => f.write_str("lt"),
            Comparison::LessThanOrEqual => f.write_str("lte"),
            Comparison::GreaterThan => f.write_str("gt"),
            Comparison::GreaterThanOrEqual => f.write_str("gte"),
        }
    }
}

/// A virtual machine function.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Function<Intrinsic> {
    /// The name of the function.
    pub name: Symbol,
    /// The number of arguments this function expects.
    pub arg_count: usize,
    /// The number of variables this function requests space for.
    pub variable_count: usize,
    /// The instructions that make up the function body.
    pub code: Vec<Instruction<Intrinsic>>,
}

impl<Intrinsic> Function<Intrinsic> {
    /// Returns a new function for a given code block.
    pub fn new(name: impl Into<Symbol>, arg_count: usize, block: CodeBlock<Intrinsic>) -> Self {
        Self {
            name: name.into(),
            arg_count,
            variable_count: block.variables,
            code: block.code,
        }
    }
}

/// A virtual machine value.
#[derive(Debug, Clone)]
pub enum Value {
    /// A value representing the lack of a value.
    Void,
    /// A signed 64-bit integer value.
    Integer(i64),
    /// A real number value (64-bit floating point).
    Real(f64),
    /// A boolean representing true or false.
    Boolean(bool),
    /// A type exposed from Rust.
    Dynamic(Dynamic),
}

impl Default for Value {
    #[inline]
    fn default() -> Self {
        Self::Void
    }
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
            value.inner()
        } else {
            None
        }
    }

    /// Returns the contained value if `T` matches the contained type and this
    /// is the final reference to the value. If the value contains another type
    /// or additional references exist, `Err(self)` will be returned. Otherwise,
    /// the original value will be returned.
    pub fn try_into_dynamic<T: DynamicValue>(self) -> Result<T, Self> {
        // Before we consume the value, verify we have the correct type.
        if self.as_dynamic::<T>().is_some() {
            // We can now destruct self safely without worrying about needing to
            // return an error.
            if let Self::Dynamic(value) = self {
                value.try_into_inner().map_err(Self::Dynamic)
            } else {
                unreachable!()
            }
        } else {
            Err(self)
        }
    }

    /// Returns the contained value, if it was one originally created with
    /// [`Value::dynamic()`] and `T` is the same type. If the value contains
    /// another type, `Err(self)` will be returned. Otherwise, the original
    /// value will be returned.
    ///
    /// Because dynamic values are cheaply cloned by wrapping the value in an
    /// [`std::sync::Arc`], this method will return a clone if there are any
    /// other instances that point to the same contained value. If this is the
    /// final instance of this value, the contained value will be returned
    /// without additional allocations.
    pub fn into_dynamic<T: DynamicValue + Clone>(self) -> Result<T, Self> {
        // Before we consume the value, verify we have the correct type.
        if self.as_dynamic::<T>().is_some() {
            // We can now destruct self safely without worrying about needing to
            // return an error.
            if let Self::Dynamic(value) = self {
                value.into_inner().map_err(Self::Dynamic)
            } else {
                unreachable!()
            }
        } else {
            Err(self)
        }
    }

    /// If this value is a [`Value::Integer`], this function returns the
    /// contained value. Otherwise, `None` is returned.
    #[must_use]
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Value::Integer(value) => Some(*value),
            Value::Dynamic(dynamic) => dynamic.as_i64(),
            _ => None,
        }
    }

    /// If this value is a [`Value::Real`], this function returns the
    /// contained value. Otherwise, `None` is returned.
    #[must_use]
    pub fn as_f64(&self) -> Option<f64> {
        if let Value::Real(value) = self {
            Some(*value)
        } else {
            None
        }
    }

    /// Converts this value to another kind, if possible.
    #[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
    pub fn convert<Env>(&self, kind: &ValueKind, environment: &Env) -> Result<Self, FaultKind>
    where
        Env: Environment,
    {
        let converted = match kind {
            ValueKind::Integer => match self {
                Value::Void => None,
                Value::Integer(value) => Some(Value::Integer(*value)),
                Value::Real(value) => Some(Value::Integer(*value as i64)),
                Value::Boolean(value) => {
                    if *value {
                        Some(Value::Integer(1))
                    } else {
                        Some(Value::Integer(0))
                    }
                }
                Value::Dynamic(value) => value.as_i64().map(Value::Integer),
            },
            ValueKind::Real => match self {
                Value::Integer(value) => Some(Value::Real(*value as f64)),
                Value::Real(value) => Some(Value::Real(*value)),
                _ => None,
            },
            ValueKind::Boolean => Some(Value::Boolean(self.is_truthy())),
            ValueKind::Dynamic(kind) => Some(environment.convert(self, kind)?),
            ValueKind::Void => None,
        };

        converted.ok_or_else(|| {
            FaultKind::invalid_type(
                format!("@received-kind cannot be converted to {kind}"),
                self.clone(),
            )
        })
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
            Value::Real(value) => value.abs() >= f64::EPSILON,
            Value::Boolean(value) => *value,
            Value::Dynamic(value) => value.is_truthy(),
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
            Value::Dynamic(value) => ValueKind::Dynamic(value.kind()),
            Value::Void => ValueKind::Void,
        }
    }

    /// Returns true if value contained supports hashing.
    ///
    /// Using [`Hash`] on a value that does not support hashing will not panic,
    /// but unique hash values will not be generated.
    #[must_use]
    pub fn implements_hash(&self) -> bool {
        struct NullHasher;
        impl std::hash::Hasher for NullHasher {
            fn finish(&self) -> u64 {
                0
            }

            fn write(&mut self, _bytes: &[u8]) {}
        }

        self.try_hash(&mut NullHasher)
    }

    /// Attempts to compute a hash over this value. Returns true if the value
    /// contained supports hashing.
    ///
    /// The `state` may be mutated even if the contained value does not contain
    /// a hashable value.
    pub fn try_hash<H: Hasher>(&self, state: &mut H) -> bool {
        match self {
            Value::Void => state.write_u8(0),
            Value::Integer(value) => {
                state.write_u8(1);
                value.hash(state);
            }
            Value::Boolean(value) => {
                state.write_u8(2);
                value.hash(state);
            }
            Value::Dynamic(value) => {
                state.write_u8(3);
                value.type_id().hash(state);

                if !value.hash(state) {
                    return false;
                }
            }
            Value::Real(_) => return false,
        }
        true
    }
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.try_hash(state);
    }
}

impl Eq for Value {}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Integer(lhs), Self::Integer(rhs)) => lhs == rhs,
            (Self::Real(lhs), Self::Real(rhs)) => real_total_eq(*lhs, *rhs),
            (Self::Boolean(lhs), Self::Boolean(rhs)) => lhs == rhs,
            (Self::Void, Self::Void) => true,
            (Self::Dynamic(lhs), Self::Dynamic(rhs)) => lhs
                .partial_eq(other)
                .or_else(|| rhs.partial_eq(self))
                .unwrap_or(false),
            (Self::Dynamic(lhs), _) => lhs.partial_eq(other).unwrap_or(false),
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

#[test]
fn real_eq_tests() {
    assert!(real_total_eq(0.1, 0.1));
    assert!(!real_total_eq(0.1 + f64::EPSILON, 0.1));
    assert!(real_total_eq(f64::NAN, f64::NAN));
    assert!(!real_total_eq(f64::NAN, -f64::NAN));
    assert!(!real_total_eq(f64::NAN, 0.1));
    assert!(!real_total_eq(f64::NAN, f64::INFINITY));
    assert!(!real_total_eq(f64::NAN, f64::NEG_INFINITY));
    assert!(real_total_eq(f64::INFINITY, f64::INFINITY));
    assert!(!real_total_eq(f64::INFINITY, f64::NEG_INFINITY));
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

impl PartialOrd for Value {
    #[inline]
    fn partial_cmp(&self, right: &Self) -> Option<Ordering> {
        match self {
            Value::Integer(left) => match right {
                Value::Integer(right) => Some(left.cmp(right)),
                Value::Dynamic(right_dynamic) => {
                    dynamic::cmp(right, right_dynamic, self).map(Ordering::reverse)
                }
                _ => None,
            },
            Value::Real(left) => match right {
                Value::Real(right) => Some(left.total_cmp(right)),
                Value::Dynamic(right_dynamic) => {
                    dynamic::cmp(right, right_dynamic, self).map(Ordering::reverse)
                }
                _ => None,
            },
            Value::Boolean(left) => match right {
                Value::Boolean(right) => Some(left.cmp(right)),
                Value::Dynamic(right_dynamic) => {
                    dynamic::cmp(right, right_dynamic, self).map(Ordering::reverse)
                }
                _ => None,
            },
            Value::Dynamic(left_dynamic) => dynamic::cmp(self, left_dynamic, right),
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
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ValueKind {
    /// A signed 64-bit integer value.
    Integer,
    /// A real number value (64-bit floating point).
    Real,
    /// A boolean representing true or false.
    Boolean,
    /// A dynamically exposed Rust type.
    Dynamic(Symbol),
    /// A value representing the lack of a value.
    Void,
}

impl ValueKind {
    /// Returns this kind as a string.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            ValueKind::Integer => "Integer",
            ValueKind::Real => "Real",
            ValueKind::Boolean => "Boolean",
            ValueKind::Void => "Void",
            ValueKind::Dynamic(name) => name,
        }
    }
}

impl<'a> From<&'a str> for ValueKind {
    fn from(kind: &'a str) -> Self {
        match kind {
            "Integer" => ValueKind::Integer,
            "Real" => ValueKind::Real,
            "Boolean" => ValueKind::Boolean,
            _ => ValueKind::Dynamic(Symbol::from(kind)),
        }
    }
}

impl From<Symbol> for ValueKind {
    fn from(kind: Symbol) -> Self {
        match &*kind {
            "Integer" => ValueKind::Integer,
            "Real" => ValueKind::Real,
            "Boolean" => ValueKind::Boolean,
            _ => ValueKind::Dynamic(kind),
        }
    }
}

impl Display for ValueKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Module<Intrinsic> {
    contents: StdHashMap<Symbol, ModuleItem>,
    vtable: Vec<VtableEntry<Intrinsic>>,
}
impl<Intrinsic> Default for Module<Intrinsic> {
    fn default() -> Self {
        Self {
            contents: StdHashMap::default(),
            vtable: Vec::default(),
        }
    }
}

impl<Intrinsic> Module<Intrinsic> {
    // #[must_use]
    // pub fn with_function(mut self, name: impl Into<Symbol>, function: Function) -> Self {
    //     self.define_function(name, function);
    //     self
    // }

    fn define_vtable_entry(
        &mut self,
        name: impl Into<Symbol>,
        entry: VtableEntry<Intrinsic>,
    ) -> usize {
        let vtable_index = self.vtable.len();
        self.contents
            .insert(name.into(), ModuleItem::Function(vtable_index));
        self.vtable.push(entry);
        vtable_index
    }

    pub fn define_function(&mut self, function: Function<Intrinsic>) -> usize {
        self.define_vtable_entry(function.name.clone(), VtableEntry::Function(function))
    }

    pub fn define_native_function(
        &mut self,
        name: impl Into<Symbol>,
        function: impl NativeFunction + 'static,
    ) -> usize {
        self.define_vtable_entry(name, VtableEntry::NativeFunction(Arc::new(function)))
    }
}

#[derive(Clone)]
enum VtableEntry<Intrinsic> {
    Function(Function<Intrinsic>),
    NativeFunction(Arc<dyn NativeFunction>),
}

impl<Intrinsic> Debug for VtableEntry<Intrinsic>
where
    Intrinsic: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Function(arg0) => f.debug_tuple("Function").field(arg0).finish(),
            Self::NativeFunction(_arg0) => f.debug_tuple("NativeFunction").finish(),
        }
    }
}

impl<Intrinsic> PartialEq for VtableEntry<Intrinsic>
where
    Intrinsic: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Function(l0), Self::Function(r0)) => l0 == r0,
            (Self::NativeFunction(l0), Self::NativeFunction(r0)) => l0.as_ptr() == r0.as_ptr(),
            _ => false,
        }
    }
}

/// A native function for Bud.
pub trait NativeFunction {
    /// Invoke this function with `args`.
    fn invoke(&self, args: &mut PoppedValues<'_>) -> Result<Value, FaultKind>;

    #[doc(hidden)]
    fn as_ptr(&self) -> *const u8;
}

impl<T> NativeFunction for T
where
    T: for<'a, 'b> Fn(&'b mut PoppedValues<'a>) -> Result<Value, FaultKind>,
{
    fn invoke(&self, args: &mut PoppedValues<'_>) -> Result<Value, FaultKind> {
        self(args)
    }

    fn as_ptr(&self) -> *const u8 {
        (self as *const T).cast::<u8>()
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum ModuleItem {
    Function(usize),
    // Module(Module),
}

/// A Bud virtual machine instance.
///
/// Each instance of this type has its own sandboxed environment. Its stack
/// space, function declarations, and [`Environment`] are unique from all other
/// instances of Bud with the exception that [`Symbol`]s are tracked globally.
///
/// # General Virtual Machine design
///
/// At the core of this type is a [`Stack`], which is a list of [`Value`]s. The
/// virtual machine divides the stack into "frames" (regions of [`Value`]s) as
/// it executes and calls functions.
///
/// Each stack frame is divided into two sections: arguments that were passed to
/// the function, and space for local variables. Stack frames are automatically
/// managed by the virtual machine.
///
/// The only time [`Value`]s need to be pushed to the stack directly is when
/// calling a function. Each argument being passed to the function is pushed to
/// the stack, and the virtual machine adopts the pushed values as part of the
/// called function's stack frame.
///
/// This example demonstrates a basic function that takes one argument and uses
/// 1 local variable. It performs the equivalent of creating a string like
/// `Hello, {name}!`.
///
/// ```rust
/// use std::borrow::Cow;
/// use budvm::{VirtualMachine, Function, Instruction, Value, ValueOrSource, Destination, Symbol};
///
/// let greet = Function {
///     name: Symbol::from("greet"),
///     arg_count: 1,
///     variable_count: 1,
///     code: vec![
///         Instruction::Add {
///             left: ValueOrSource::Value(Value::dynamic(String::from("Hello, "))),
///             right: ValueOrSource::Argument(0),
///             destination: Destination::Variable(0),
///         },
///         Instruction::Add {
///             left: ValueOrSource::Variable(0),
///             right: ValueOrSource::Value(Value::dynamic(String::from("!"))),
///             destination: Destination::Return,
///         },
///     ],
/// };
///
/// let mut vm = VirtualMachine::empty().with_function(greet);
/// let result: String = vm
///     .run(
///         Cow::Borrowed(&[
///             Instruction::Push(ValueOrSource::Value(Value::dynamic(String::from("Ferris")))),
///             Instruction::Call {
///                 vtable_index: Some(0),
///                 arg_count: 1,
///                 destination: Destination::Stack,
///             },
///         ]),
///         0,
///     )
///     .unwrap();
/// assert_eq!(result, "Hello, Ferris!");
/// ```
///
/// When the virtual machine finishes executing [`Instruction::Call`],
/// [`Instruction::CallIntrinsic`], or [`Instruction::CallInstance`], the return
/// value is placed in the correct location and the stack is cleaned up to
/// remove all pushed arguments and local variables of the function being
/// called.
///
/// The Rust interface will automatically pop a value from the stack upon
/// returning. The [`FromStack`] trait allows a type to be converted seamlessly
/// as in the above example.
///
/// The previous example also highlights one other interesting aspect of the
/// virtual machine: all heap-allocated types are grouped into a single
/// [`Dynamic`] type. This means that the virtual machine doesn't actually know
/// anything about the `String` type. The virtual machine knows how to perform
/// operations with [`Dynamic`] values, and any Rust type that implements
/// [`DynamicValue`] can be used in the virtual machine.
///
/// Each [`Instruction`] variant is documented with its expected behavior.
///
/// # Custom Environments
///
/// The virtual machine has several opportunities to customize its behavior. For
/// default behavior, [`Environment`] is implemented for `()`.
///
/// There are multiple reasons to implement a custom [`Environment`]:
///
/// * The [`Environment::Intrinsic`] associated type allows extending the
///   virtual machine with intrinsic functions. Bud uses this to initialize map
///   and list literals at runtime via `NewMap` and `NewList` intrinsics.
/// * The [`Environment::String`] type can be replaced to use another string
///   type.
/// * The [`Environment::step()`] function can be overriden to pause execution
///   conditionally.
///
///
#[derive(Debug, Default, Clone, PartialEq)]
pub struct VirtualMachine<Env>
where
    Env: Environment,
{
    /// The stack for this virtual machine. Take care when manually manipulating
    /// the stack.
    pub stack: Stack,
    persistent_variables: Vec<Symbol>,
    local_module: Module<Env::Intrinsic>,
    environment: Env,
}

impl VirtualMachine<()> {
    /// Returns a default instance of Bud with no custom [`Environment`]
    #[must_use]
    pub fn empty() -> Self {
        Self::default_for(())
    }
}

impl<Env> VirtualMachine<Env>
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
            persistent_variables: Vec::new(),
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

    /// Returns a list of persistent variables defined with
    /// [`Scope::define_persistent_variable()`]
    pub fn persistent_variables(&self) -> &[Symbol] {
        &self.persistent_variables
    }

    /// Registers a function with the provided name and returns self. This is a
    /// builder-style function.
    #[must_use]
    pub fn with_function(mut self, function: Function<Env::Intrinsic>) -> Self {
        self.define_function(function);
        self
    }

    /// Registers a function with the provided name and returns self. This is a
    /// builder-style function.
    #[must_use]
    pub fn with_native_function(
        mut self,
        name: impl Into<Symbol>,
        function: impl NativeFunction + 'static,
    ) -> Self {
        self.define_native_function(name, function);
        self
    }

    /// Defines a native function with the provided name.
    pub fn define_native_function(
        &mut self,
        name: impl Into<Symbol>,
        function: impl NativeFunction + 'static,
    ) -> usize {
        self.local_module.define_native_function(name, function)
    }

    /// Runs a set of instructions.
    pub fn call<'a, Output: FromStack, Args, ArgsIter>(
        &'a mut self,
        function: &Symbol,
        arguments: Args,
    ) -> Result<Output, Fault<'_, Env, Output>>
    where
        Args: IntoIterator<Item = Value, IntoIter = ArgsIter>,
        ArgsIter: Iterator<Item = Value> + ExactSizeIterator + DoubleEndedIterator,
    {
        match self.local_module.contents.get(function) {
            Some(ModuleItem::Function(vtable_index)) => {
                let arg_count = self.stack.extend(arguments)?;
                // TODO It'd be nice to not have to have an allocation here
                self.run(
                    Cow::Owned(vec![Instruction::Call {
                        vtable_index: Some(*vtable_index),
                        arg_count,
                        destination: Destination::Return,
                    }]),
                    0,
                )
            }
            None => Err(Fault::from(FaultKind::UnknownFunction {
                kind: ValueKind::Void,
                name: function.clone(),
            })),
        }
    }

    /// Runs a set of instructions, allocating space for `variable_count`
    /// variables to be used by `instructions`. When this function returns, the
    /// stack space for the variables will be removed.
    pub fn run<'a, Output: FromStack>(
        &'a mut self,
        instructions: Cow<'a, [Instruction<Env::Intrinsic>]>,
        variable_count: usize,
    ) -> Result<Output, Fault<'a, Env, Output>> {
        self.run_internal(instructions, variable_count, false)
    }

    /// Runs a set of instructions without modifying the stack before executing.
    ///
    /// The top `variable_count` slots on the stack are considered variables
    /// while executing `instructions`.
    ///
    /// When the execution finishes, the stack will not be truncated in any way.
    ///
    /// This function can be used to build an interactive environment, like a
    /// [REPL][repl].
    ///
    /// [repl]:
    ///     https://en.wikipedia.org/wiki/Read%E2%80%93eval%E2%80%93print_loop
    pub fn run_interactive<'a, Output: FromStack>(
        &'a mut self,
        instructions: Cow<'a, [Instruction<Env::Intrinsic>]>,
        variable_count: usize,
    ) -> Result<Output, Fault<'a, Env, Output>> {
        self.run_internal(instructions, variable_count, true)
    }

    fn run_internal<'a, Output: FromStack>(
        &'a mut self,
        instructions: Cow<'a, [Instruction<Env::Intrinsic>]>,
        variable_count: usize,
        interactive: bool,
    ) -> Result<Output, Fault<'a, Env, Output>> {
        if !interactive && variable_count > 0 {
            self.stack.grow_by(variable_count)?;
        }

        let return_offset = self.stack.len();
        let variables_offset = return_offset
            .checked_sub(variable_count)
            .ok_or(FaultKind::StackUnderflow)?;
        let returned_value = match (StackFrame {
            module: &self.local_module,
            stack: &mut self.stack,
            environment: &mut self.environment,
            return_offset,
            destination: Destination::Return,
            variables_offset,
            arg_offset: 0,
            return_value: None,
            vtable_index: None,
            operation_index: 0,
            _output: PhantomData,
        }
        .execute_operations(&instructions))
        {
            Err(Fault {
                kind: FaultOrPause::Pause(paused_evaluation),
                stack,
            }) => {
                let paused_evaluation = PausedExecution {
                    context: Some(self),
                    operations: Some(instructions),
                    stack: paused_evaluation.stack,
                    _return: PhantomData,
                };
                return Err(Fault {
                    kind: FaultOrPause::Pause(paused_evaluation),
                    stack,
                });
            }
            other => other?,
        };
        if interactive {
            self.stack.truncate(return_offset);
        } else {
            self.stack.truncate(variables_offset);
        }
        Output::from_value(returned_value).map_err(Fault::from)
    }

    fn resume<'a, Output: FromStack>(
        &'a mut self,
        operations: Cow<'a, [Instruction<Env::Intrinsic>]>,
        mut paused_stack: VecDeque<PausedFrame>,
    ) -> Result<Output, Fault<'a, Env, Output>> {
        let first_frame = paused_stack.pop_front().expect("at least one frame");
        let value = match (StackFrame {
            module: &self.local_module,
            stack: &mut self.stack,
            environment: &mut self.environment,
            return_offset: first_frame.return_offset,
            destination: first_frame.destination,
            variables_offset: first_frame.variables_offset,
            arg_offset: first_frame.arg_offset,
            return_value: first_frame.return_value,
            vtable_index: first_frame.vtable_index,
            operation_index: first_frame.operation_index,
            _output: PhantomData,
        }
        .resume_executing_execute_operations(&operations, paused_stack))
        {
            Ok(value) => value,
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
        };
        Output::from_value(value).map_err(Fault::from)
    }

    // /// Compiles `source` and executes it in this context. Any declarations will
    // /// persist in the virtual machine, but all local variables will be removed
    // /// from the stack upon completion.
    // ///
    // /// To enable persisting of local variables, use [`Bud::evaluate()`].
    // pub fn run_source<Output: FromStack>(
    //     &mut self,
    //     source: &str,
    // ) -> Result<Output, Fault<'_, Env, Output>> {
    //     let unit = parse(source)?;
    //     unit.compile(self)?.execute_in(self)
    // }
}

impl<Env> Scope for VirtualMachine<Env>
where
    Env: Environment,
{
    type Environment = Env;

    fn resolve_function_vtable_index(&self, name: &Symbol) -> Option<usize> {
        if let Some(module_item) = self.local_module.contents.get(name) {
            match module_item {
                ModuleItem::Function(index) => Some(*index),
                // ModuleItem::Module(_) => None,
            }
        } else {
            None
        }
    }

    fn map_each_symbol(&self, callback: &mut impl FnMut(Symbol, ScopeSymbolKind)) {
        // Take care to order the functions based on their vtable index
        let mut functions = Vec::with_capacity(self.local_module.vtable.len());
        for (symbol, item) in &self.local_module.contents {
            match item {
                ModuleItem::Function(index) => functions.push((symbol.clone(), *index)),
            }
        }

        functions.sort_by(|a, b| a.1.cmp(&b.1));

        for (symbol, _) in functions {
            callback(symbol, ScopeSymbolKind::Function);
        }

        for variable in &self.persistent_variables {
            callback(variable.clone(), ScopeSymbolKind::Variable);
        }
    }

    fn define_function(&mut self, function: Function<Env::Intrinsic>) -> Option<usize> {
        Some(self.local_module.define_function(function))
    }

    fn define_persistent_variable(&mut self, name: Symbol, variable: crate::ir::Variable) {
        if variable.index() >= self.persistent_variables.len() {
            self.persistent_variables
                .resize_with(variable.index() + 1, || Symbol::from(""));
        }

        self.persistent_variables[variable.index()] = name;
    }
}

enum FlowControl {
    Return(Value),
    JumpTo(usize),
}

#[derive(Debug)]
struct StackFrame<'a, Env, Output>
where
    Env: Environment,
{
    module: &'a Module<Env::Intrinsic>,
    stack: &'a mut Stack,
    environment: &'a mut Env,
    // Each stack frame cannot pop below this offset.
    return_offset: usize,
    destination: Destination,
    variables_offset: usize,
    arg_offset: usize,
    return_value: Option<Value>,

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
        operations: &[Instruction<Env::Intrinsic>],
        mut resume_from: VecDeque<PausedFrame>,
    ) -> Result<Value, Fault<'static, Env, Output>> {
        if let Some(call_to_resume) = resume_from.pop_front() {
            // We were calling a function when this happened. We need to finish the call.
            let vtable_index = call_to_resume
                .vtable_index
                .expect("can only resume a called function");
            let function = match &self.module.vtable[vtable_index] {
                VtableEntry::Function(function) => function,
                VtableEntry::NativeFunction(_) => unreachable!("cannot resume a native function"),
            };
            let mut running_frame = StackFrame {
                module: self.module,
                stack: self.stack,
                environment: self.environment,
                return_offset: call_to_resume.return_offset,
                destination: call_to_resume.destination,
                variables_offset: call_to_resume.variables_offset,
                arg_offset: call_to_resume.arg_offset,
                return_value: call_to_resume.return_value,
                vtable_index: call_to_resume.vtable_index,
                operation_index: call_to_resume.operation_index,
                _output: PhantomData,
            };
            let returned_value = match running_frame
                .resume_executing_execute_operations(&function.code, resume_from)
            {
                Ok(value) => value,
                Err(Fault {
                    kind: FaultOrPause::Pause(mut paused),
                    stack,
                }) => {
                    paused.stack.push_front(PausedFrame {
                        return_offset: self.return_offset,
                        arg_offset: self.arg_offset,
                        variables_offset: self.variables_offset,
                        return_value: self.return_value.take(),
                        vtable_index: self.vtable_index,
                        operation_index: self.operation_index,
                        destination: self.destination,
                    });
                    return Err(Fault {
                        kind: FaultOrPause::Pause(paused),
                        stack,
                    });
                }
                Err(err) => return Err(err),
            };

            self.clean_stack_after_call(
                call_to_resume.arg_offset,
                call_to_resume.destination,
                returned_value,
            )?;

            // The call that was executing when we paused has finished, we can
            // now resume executing our frame's instructions.
        }

        self.execute_operations(operations)
    }
    fn execute_operations(
        &mut self,
        operations: &[Instruction<Env::Intrinsic>],
    ) -> Result<Value, Fault<'static, Env, Output>> {
        loop {
            if matches!(self.environment.step(), ExecutionBehavior::Pause) {
                let mut stack = VecDeque::new();
                stack.push_front(PausedFrame {
                    return_offset: self.return_offset,
                    arg_offset: self.arg_offset,
                    variables_offset: self.variables_offset,
                    return_value: self.return_value.take(),
                    vtable_index: self.vtable_index,
                    operation_index: self.operation_index,
                    destination: self.destination,
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
            let operation = if let Some(operation) = operation {
                operation
            } else {
                // Implicit return;
                let return_value = self.return_value.take().unwrap_or_else(|| {
                    if self.return_offset < self.stack.len() {
                        std::mem::take(&mut self.stack[self.return_offset])
                    } else {
                        Value::Void
                    }
                });
                return Ok(return_value);
            };
            self.operation_index += 1;
            match self.execute_operation(operation) {
                Ok(None) => {}
                Ok(Some(FlowControl::JumpTo(op_index))) => {
                    self.operation_index = op_index;
                }
                Ok(Some(FlowControl::Return(value))) => {
                    return Ok(value);
                }
                Err(mut fault) => {
                    if let FaultOrPause::Pause(paused_frame) = &mut fault.kind {
                        paused_frame.stack.push_front(PausedFrame {
                            return_offset: self.return_offset,
                            arg_offset: self.arg_offset,
                            variables_offset: self.variables_offset,
                            return_value: self.return_value.take(),
                            vtable_index: self.vtable_index,
                            operation_index: self.operation_index,
                            destination: self.destination,
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

    #[allow(clippy::too_many_lines)]
    fn execute_operation(
        &mut self,
        operation: &Instruction<Env::Intrinsic>,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        match operation {
            Instruction::JumpTo(instruction_index) => {
                Ok(Some(FlowControl::JumpTo(*instruction_index)))
            }
            Instruction::Add {
                left,
                right,
                destination,
            } => self.checked_add(left, right, *destination),
            Instruction::Sub {
                left,
                right,
                destination,
            } => self.checked_sub(left, right, *destination),
            Instruction::Multiply {
                left,
                right,
                destination,
            } => self.checked_mul(left, right, *destination),
            Instruction::Divide {
                left,
                right,
                destination,
            } => self.checked_div(left, right, *destination),
            Instruction::LogicalAnd {
                left,
                right,
                destination,
            } => self.and(left, right, *destination),
            Instruction::LogicalOr {
                left,
                right,
                destination,
            } => self.or(left, right, *destination),
            Instruction::LogicalXor {
                left,
                right,
                destination,
            } => self.xor(left, right, *destination),
            Instruction::BitwiseAnd {
                left,
                right,
                destination,
            } => self.integer_op(left, right, *destination, |a, b| Ok(a & b)),
            Instruction::BitwiseOr {
                left,
                right,
                destination,
            } => self.integer_op(left, right, *destination, |a, b| Ok(a | b)),
            Instruction::BitwiseXor {
                left,
                right,
                destination,
            } => self.integer_op(left, right, *destination, |a, b| Ok(a ^ b)),
            Instruction::ShiftLeft {
                left,
                right,
                destination,
            } => self.integer_op(left, right, *destination, |a, b| {
                if b < 64 {
                    Ok(a << b)
                } else {
                    Ok(0)
                }
            }),
            Instruction::ShiftRight {
                left,
                right,
                destination,
            } => self.integer_op(left, right, *destination, |a, b| {
                if b < 64 {
                    Ok(a >> b)
                } else {
                    Ok(0)
                }
            }),
            Instruction::LogicalNot {
                value: left,
                destination,
            } => self.not(left, *destination),
            Instruction::BitwiseNot {
                value: left,
                destination,
            } => self.bitnot(left, *destination),
            Instruction::Convert {
                value,
                kind,
                destination,
            } => self.convert(value, kind, *destination),
            Instruction::If {
                condition: value,
                false_jump_to,
            } => self.r#if(value, *false_jump_to),
            Instruction::Compare {
                comparison,
                left,
                right,
                action,
            } => self.compare(*comparison, left, right, *action),
            Instruction::Push(value) => {
                match value {
                    ValueOrSource::Value(value) => self.stack.push(value.clone())?,
                    ValueOrSource::Argument(arg) => self.push_arg(*arg)?,
                    ValueOrSource::Variable(variable) => self.push_var(*variable)?,
                }

                Ok(None)
            }
            Instruction::Return(value) => {
                let value = match value {
                    Some(ValueOrSource::Value(value)) => value.clone(),
                    Some(ValueOrSource::Variable(source)) => {
                        self.resolve_variable(*source)?.clone()
                    }
                    Some(ValueOrSource::Argument(source)) => {
                        self.resolve_argument(*source)?.clone()
                    }
                    None => self.return_value.take().unwrap_or_default(),
                };

                Ok(Some(FlowControl::Return(value)))
            }
            Instruction::Load {
                variable_index,
                value,
            } => self.load(*variable_index, value),
            Instruction::Call {
                vtable_index,
                arg_count,
                destination,
            } => self.call(*vtable_index, *arg_count, *destination),
            Instruction::CallIntrinsic {
                intrinsic,
                arg_count,
                destination,
            } => self.intrinsic(intrinsic, *arg_count, *destination),
            Instruction::CallInstance {
                target,
                name,
                arg_count,
                destination,
            } => self.call_instance(target.as_ref(), name, *arg_count, *destination),
        }
    }

    fn clean_stack_after_call(
        &mut self,
        arg_offset: usize,
        destination: Destination,
        returned_value: Value,
    ) -> Result<(), Fault<'static, Env, Output>> {
        // Remove everything from arguments on.
        self.stack.remove_range(arg_offset..);

        match destination {
            Destination::Variable(variable) => {
                *self.resolve_variable_mut(variable)? = returned_value;
                Ok(())
            }
            Destination::Stack => self.stack.push(returned_value).map_err(Fault::from),
            Destination::Return => {
                self.return_value = Some(returned_value);
                Ok(())
            }
        }
    }

    fn resolve_variable(&self, index: usize) -> Result<&Value, FaultKind> {
        if let Some(index) = self.variables_offset.checked_add(index) {
            if index < self.return_offset {
                return Ok(&self.stack[index]);
            }
        }
        Err(FaultKind::InvalidVariableIndex)
    }

    fn resolve_argument(&self, index: usize) -> Result<&Value, FaultKind> {
        if let Some(index) = self.arg_offset.checked_add(index) {
            if index < self.variables_offset {
                return Ok(&self.stack[index]);
            }
        }
        Err(FaultKind::InvalidArgumentIndex)
    }

    fn resolve_variable_mut(&mut self, index: usize) -> Result<&mut Value, FaultKind> {
        if let Some(index) = self.variables_offset.checked_add(index) {
            if index < self.return_offset {
                return Ok(&mut self.stack[index]);
            }
        }
        Err(FaultKind::InvalidVariableIndex)
    }

    fn resolve_value_source_mut(&mut self, value: Destination) -> Result<&mut Value, FaultKind> {
        match value {
            Destination::Variable(index) => self.resolve_variable_mut(index),
            Destination::Stack => {
                self.stack.grow_by(1)?;
                self.stack.top_mut()
            }
            Destination::Return => {
                if self.return_value.is_none() {
                    self.return_value = Some(Value::Void);
                }
                Ok(self.return_value.as_mut().expect("always initialized"))
            }
        }
    }

    fn resolve_value_or_source<'v>(
        &'v self,
        value: &'v ValueOrSource,
    ) -> Result<&'v Value, FaultKind> {
        match value {
            ValueOrSource::Argument(index) => self.resolve_argument(*index),
            ValueOrSource::Variable(index) => self.resolve_variable(*index),
            ValueOrSource::Value(value) => Ok(value),
        }
    }

    fn r#if(
        &mut self,
        value: &ValueOrSource,
        false_jump_to: usize,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        if self.resolve_value_or_source(value)?.is_truthy() {
            Ok(None)
        } else {
            Ok(Some(FlowControl::JumpTo(false_jump_to)))
        }
    }

    #[allow(clippy::unnecessary_wraps)] // makes caller more clean
    fn equality<const INVERSE: bool>(left: &Value, right: &Value) -> bool {
        let mut result = left.eq(right);
        if INVERSE {
            result = !result;
        }
        result
    }

    fn compare_values(
        left: &Value,
        right: &Value,
        matcher: impl FnOnce(Ordering) -> bool,
    ) -> Result<bool, Fault<'static, Env, Output>> {
        if let Some(ordering) = left.partial_cmp(right) {
            Ok(matcher(ordering))
        } else {
            Err(Fault::type_mismatch(
                "invalid comparison between @expected and `@received-value` (@received-type)",
                left.kind(),
                right.clone(),
            ))
        }
    }

    fn compare(
        &mut self,
        comparison: Comparison,
        left: &ValueOrSource,
        right: &ValueOrSource,
        result: CompareAction,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let left = self.resolve_value_or_source(left)?;
        let right = self.resolve_value_or_source(right)?;

        let comparison_result = match comparison {
            Comparison::Equal => Self::equality::<false>(left, right),
            Comparison::NotEqual => Self::equality::<true>(left, right),
            Comparison::LessThan => {
                Self::compare_values(left, right, |ordering| ordering == Ordering::Less)?
            }
            Comparison::LessThanOrEqual => Self::compare_values(left, right, |ordering| {
                matches!(ordering, Ordering::Less | Ordering::Equal)
            })?,
            Comparison::GreaterThan => {
                Self::compare_values(left, right, |ordering| ordering == Ordering::Greater)?
            }
            Comparison::GreaterThanOrEqual => Self::compare_values(left, right, |ordering| {
                matches!(ordering, Ordering::Greater | Ordering::Equal)
            })?,
        };

        match result {
            CompareAction::Store(dest) => {
                *self.resolve_value_source_mut(dest)? = Value::Boolean(comparison_result);

                Ok(None)
            }
            CompareAction::JumpIfFalse(target) => {
                if comparison_result {
                    Ok(None)
                } else {
                    Ok(Some(FlowControl::JumpTo(target)))
                }
            }
        }
    }

    fn push_var(&mut self, variable: usize) -> Result<(), Fault<'static, Env, Output>> {
        if let Some(stack_offset) = self.variables_offset.checked_add(variable) {
            if stack_offset < self.return_offset {
                let value = self.stack[stack_offset].clone();
                self.stack.push(value)?;
                return Ok(());
            }
        }
        Err(Fault::from(FaultKind::InvalidVariableIndex))
    }

    fn push_arg(&mut self, arg: usize) -> Result<(), Fault<'static, Env, Output>> {
        if let Some(stack_offset) = self.arg_offset.checked_add(arg) {
            if stack_offset < self.variables_offset {
                let value = self.stack[stack_offset].clone();
                self.stack.push(value)?;
                return Ok(());
            }
        }
        Err(Fault::from(FaultKind::InvalidArgumentIndex))
    }

    fn load(
        &mut self,
        variable: usize,
        value: &ValueOrSource,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let value = self.resolve_value_or_source(value)?;
        *self.resolve_variable_mut(variable)? = value.clone();

        Ok(None)
    }

    fn call(
        &mut self,
        vtable_index: Option<usize>,
        arg_count: usize,
        destination: Destination,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let vtable_index = vtable_index
            .or(self.vtable_index)
            .ok_or(FaultKind::InvalidVtableIndex)?;
        let function = &self
            .module
            .vtable
            .get(vtable_index)
            .ok_or(FaultKind::InvalidVtableIndex)?;

        match function {
            VtableEntry::Function(function) => {
                assert_eq!(function.arg_count, arg_count);

                let variables_offset = self.stack.len();
                let return_offset = variables_offset + function.variable_count;
                let arg_offset = variables_offset - function.arg_count;
                if function.variable_count > 0 {
                    self.stack.grow_to(return_offset)?;
                }

                let mut frame = StackFrame {
                    module: self.module,
                    stack: self.stack,
                    environment: self.environment,
                    return_offset,
                    destination,
                    variables_offset,
                    arg_offset,
                    return_value: None,
                    vtable_index: Some(vtable_index),
                    operation_index: 0,
                    _output: PhantomData,
                };
                let returned_value = frame.execute_operations(&function.code)?;

                self.clean_stack_after_call(arg_offset, destination, returned_value)?;

                Ok(None)
            }
            VtableEntry::NativeFunction(function) => {
                let return_offset = self.stack.len();
                let arg_offset = return_offset.checked_sub(arg_count);
                match arg_offset {
                    Some(arg_offset) if arg_offset >= self.return_offset => {}
                    _ => return Err(Fault::stack_underflow()),
                };

                let produced_value = function.invoke(&mut self.stack.pop_n(arg_count))?;
                match destination {
                    Destination::Variable(variable) => {
                        *self.resolve_variable_mut(variable)? = produced_value;
                    }
                    Destination::Stack => {
                        self.stack.push(produced_value)?;
                    }
                    Destination::Return => {
                        self.return_value = Some(produced_value);
                    }
                }
                Ok(None)
            }
        }
    }

    fn call_instance(
        &mut self,
        target: Option<&ValueOrSource>,
        name: &Symbol,
        arg_count: usize,
        destination: Destination,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        // To prevent overlapping a mutable borrow of the value plus immutable
        // borrows of the stack, we temporarily take the value from where it
        // lives.
        let stack_index = match target {
            Some(ValueOrSource::Argument(index)) => {
                if let Some(stack_index) = self.arg_offset.checked_add(*index) {
                    if stack_index < self.variables_offset {
                        stack_index
                    } else {
                        return Err(Fault::from(FaultKind::InvalidArgumentIndex));
                    }
                } else {
                    return Err(Fault::from(FaultKind::InvalidArgumentIndex));
                }
            }
            Some(ValueOrSource::Variable(index)) => {
                if let Some(stack_index) = self.variables_offset.checked_add(*index) {
                    if stack_index < self.return_offset {
                        stack_index
                    } else {
                        return Err(Fault::from(FaultKind::InvalidVariableIndex));
                    }
                } else {
                    return Err(Fault::from(FaultKind::InvalidVariableIndex));
                }
            }
            Some(ValueOrSource::Value(value)) => {
                // We don't have any intrinsic functions yet, and this Value can
                // only be a literal.
                return Err(Fault::from(FaultKind::UnknownFunction {
                    kind: value.kind(),
                    name: name.clone(),
                }));
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

        // Verify the argument list is valid.
        let return_offset = self.stack.len();
        let arg_offset = return_offset.checked_sub(arg_count);
        match arg_offset {
            Some(arg_offset) if arg_offset >= self.return_offset => {}
            _ => return Err(Fault::stack_underflow()),
        };

        // Pull the target out of its current location.
        let mut target_value = Value::Void;
        std::mem::swap(&mut target_value, &mut self.stack[stack_index]);
        // Call without resolving any errors
        let result = match &mut target_value {
            Value::Dynamic(value) => value.call(name, self.stack.pop_n(arg_count)),

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
        match destination {
            Destination::Variable(variable) => {
                *self.resolve_variable_mut(variable)? = produced_value;
            }
            Destination::Stack => {
                self.stack.push(produced_value)?;
            }
            Destination::Return => {
                self.return_value = Some(produced_value);
            }
        }

        Ok(None)
    }

    fn intrinsic(
        &mut self,
        intrinsic: &Env::Intrinsic,
        arg_count: usize,
        destination: Destination,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        // Verify the argument list is valid.
        let return_offset = self.stack.len();
        let arg_offset = return_offset.checked_sub(arg_count);
        match arg_offset {
            Some(arg_offset) if arg_offset >= self.return_offset => {}
            _ => return Err(Fault::stack_underflow()),
        };
        let args = self.stack.pop_n(arg_count);

        // If there was a fault, return.
        let produced_value = self.environment.intrinsic(intrinsic, args)?;
        match destination {
            Destination::Variable(variable) => {
                *self.resolve_variable_mut(variable)? = produced_value;
            }
            Destination::Stack => {
                self.stack.push(produced_value)?;
            }
            Destination::Return => {
                self.return_value = Some(produced_value);
            }
        }

        Ok(None)
    }

    fn not(
        &mut self,
        value: &ValueOrSource,
        destination: Destination,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let value = self.resolve_value_or_source(value)?;

        *self.resolve_value_source_mut(destination)? = Value::Boolean(value.is_falsey());

        Ok(None)
    }

    fn bitnot(
        &mut self,
        value: &ValueOrSource,
        destination: Destination,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let value = self.resolve_value_or_source(value)?;
        let value = Self::extract_integer(value)?;

        *self.resolve_value_source_mut(destination)? = Value::Integer(!value);

        Ok(None)
    }

    fn convert(
        &mut self,
        value: &ValueOrSource,
        kind: &ValueKind,
        destination: Destination,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let value = self.resolve_value_or_source(value)?;
        *self.resolve_value_source_mut(destination)? = value.convert(kind, self.environment)?;

        Ok(None)
    }

    fn extract_integer(value: &Value) -> Result<i64, Fault<'static, Env, Output>> {
        if let Some(value) = value.as_i64() {
            Ok(value)
        } else {
            Err(Fault::from(FaultKind::type_mismatch(
                "operation only supports @expected, received @receoved-value (@received-kind)",
                ValueKind::Integer,
                value.clone(),
            )))
        }
    }

    fn integer_op(
        &mut self,
        left: &ValueOrSource,
        right: &ValueOrSource,
        destination: Destination,
        body: impl FnOnce(i64, i64) -> Result<i64, Fault<'static, Env, Output>>,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let left = self.resolve_value_or_source(left)?;
        let left = Self::extract_integer(left)?;
        let right = self.resolve_value_or_source(right)?;
        let right = Self::extract_integer(right)?;
        let produced_value = body(left, right)?;
        *self.resolve_value_source_mut(destination)? = Value::Integer(produced_value);

        Ok(None)
    }

    fn and(
        &mut self,
        left: &ValueOrSource,
        right: &ValueOrSource,
        destination: Destination,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let left = self.resolve_value_or_source(left)?;
        let left = left.is_truthy();

        *self.resolve_value_source_mut(destination)? = Value::Boolean(if left {
            let right = self.resolve_value_or_source(right)?;
            right.is_truthy()
        } else {
            false
        });

        Ok(None)
    }

    fn or(
        &mut self,
        left: &ValueOrSource,
        right: &ValueOrSource,
        destination: Destination,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let left = self.resolve_value_or_source(left)?;
        let left = left.is_truthy();

        *self.resolve_value_source_mut(destination)? = Value::Boolean(if left {
            true
        } else {
            let right = self.resolve_value_or_source(right)?;
            right.is_truthy()
        });

        Ok(None)
    }

    fn xor(
        &mut self,
        left: &ValueOrSource,
        right: &ValueOrSource,
        destination: Destination,
    ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
        let left = self.resolve_value_or_source(left)?;
        let left = left.is_truthy();
        let right = self.resolve_value_or_source(right)?;
        let right = right.is_truthy();

        *self.resolve_value_source_mut(destination)? = Value::Boolean(left ^ right);

        Ok(None)
    }
}

macro_rules! checked_op {
    ($name:ident, $unchecked_name:ident, $fullname:literal) => {
        impl<'a, Env, Output> StackFrame<'a, Env, Output>
        where
            Env: Environment,
        {
            fn $name(
                &mut self,
                left: &ValueOrSource,
                right: &ValueOrSource,
                result: Destination,
            ) -> Result<Option<FlowControl>, Fault<'static, Env, Output>> {
                const TYPE_MISMATCH: &str = concat!(
                    "can't ",
                    $fullname,
                    " @expected and `@received-value` (@received-type)"
                );
                let left_value = self.resolve_value_or_source(left)?;
                let right_value = self.resolve_value_or_source(right)?;

                let produced_value = match (left_value, right_value) {
                    (Value::Integer(left), Value::Integer(right)) => {
                        left.$name(*right).map_or(Value::Void, Value::Integer)
                    }
                    (Value::Real(left), Value::Real(right)) => {
                        Value::Real(left.$unchecked_name(*right))
                    }
                    (Value::Dynamic(left), right) => {
                        if let Some(value) = left.$name(right, false)? {
                            value
                        } else if let Value::Dynamic(right) = right {
                            if let Some(value) = right.$name(left_value, true)? {
                                value
                            } else {
                                return Err(Fault::type_mismatch(
                                    TYPE_MISMATCH,
                                    ValueKind::Dynamic(left.kind()),
                                    right_value.clone(),
                                ));
                            }
                        } else {
                            return Err(Fault::type_mismatch(
                                TYPE_MISMATCH,
                                ValueKind::Dynamic(left.kind()),
                                right.clone(),
                            ));
                        }
                    }
                    (left, Value::Dynamic(right)) => {
                        if let Some(value) = right.$name(left, true)? {
                            value
                        } else {
                            return Err(Fault::type_mismatch(
                                TYPE_MISMATCH,
                                ValueKind::Dynamic(right.kind()),
                                left_value.clone(),
                            ));
                        }
                    }
                    (Value::Real(_), other) => {
                        return Err(Fault::type_mismatch(
                            TYPE_MISMATCH,
                            ValueKind::Real,
                            other.clone(),
                        ))
                    }
                    (Value::Integer(_), other) => {
                        return Err(Fault::type_mismatch(
                            TYPE_MISMATCH,
                            ValueKind::Integer,
                            other.clone(),
                        ))
                    }
                    (other, _) => {
                        return Err(Fault::invalid_type(
                            concat!(
                                "`@received-value` (@received-type) does not support ",
                                $fullname
                            ),
                            other.clone(),
                        ))
                    }
                };
                *self.resolve_value_source_mut(result)? = produced_value;
                Ok(None)
            }
        }
    };
}

checked_op!(checked_add, add, "add");
checked_op!(checked_sub, sub, "subtract");
checked_op!(checked_mul, mul, "multiply");
checked_op!(checked_div, div, "divide");

/// An unexpected event occurred while executing the virtual machine.
#[derive(Debug, PartialEq)]
pub struct Fault<'a, Env, ReturnType>
where
    Env: Environment,
{
    /// The kind of fault this is.
    pub kind: FaultOrPause<'a, Env, ReturnType>,
    /// The stack trace of the virtual machine when the fault was raised.
    pub stack: Vec<FaultStackFrame>,
}

impl<Env, ReturnType> Clone for Fault<'static, Env, ReturnType>
where
    Env: Environment,
{
    fn clone(&self) -> Self {
        Self {
            kind: self.kind.clone(),
            stack: self.stack.clone(),
        }
    }
}

impl<'a, Env, ReturnType> Fault<'a, Env, ReturnType>
where
    Env: Environment,
{
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

impl<'a, Env, ReturnType> From<FaultKind> for Fault<'a, Env, ReturnType>
where
    Env: Environment,
{
    fn from(kind: FaultKind) -> Self {
        Self {
            kind: FaultOrPause::Fault(kind),
            stack: Vec::default(),
        }
    }
}

impl<'a, Env, ReturnType> std::error::Error for Fault<'a, Env, ReturnType>
where
    Env: std::fmt::Debug + Environment,
    ReturnType: std::fmt::Debug,
{
}

impl<'a, Env, ReturnType> Display for Fault<'a, Env, ReturnType>
where
    Env: Environment,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            FaultOrPause::Fault(fault) => Display::fmt(fault, f),
            FaultOrPause::Pause(_) => f.write_str("paused execution"),
        }
    }
}

/// A reason for a virtual machine [`Fault`].
#[derive(Debug, PartialEq)]
pub enum FaultOrPause<'a, Env, ReturnType>
where
    Env: Environment,
{
    /// A fault occurred while processing instructions.
    Fault(FaultKind),
    /// Execution was paused by the [`Environment`] as a result of returning
    /// [`ExecutionBehavior::Pause`] from [`Environment::step`].
    ///
    /// The contained [`PausedExecution`] can be used to resume executing the
    /// code.
    Pause(PausedExecution<'a, Env, ReturnType>),
}

impl<Env, ReturnType> Clone for FaultOrPause<'static, Env, ReturnType>
where
    Env: Environment,
{
    fn clone(&self) -> Self {
        match self {
            Self::Fault(arg0) => Self::Fault(arg0.clone()),
            Self::Pause(_) => unreachable!("paused evaluations cannot be static lifetimes"),
        }
    }
}

/// An unexpected event within the virtual machine.
#[derive(Debug, PartialEq, Clone)]
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
    /// An argument that was expected to a function was not passed.
    ArgumentMissing(Symbol),
    /// Too many arguments were passed to a function.
    TooManyArguments(Value),
    /// A value that does not support hashing was used as a key in a hash map.
    ValueCannotBeHashed(Value),
    /// A value was encountered that was out of range of valid values.
    ValueOutOfRange(&'static str),
}

impl FaultKind {
    /// An invalid type was encountered.
    ///
    /// These patterns will be replaced in `message` before being Displayed:
    ///
    /// - @received-value
    /// - @received-kind
    pub fn invalid_type(message: impl Into<String>, received: Value) -> Self {
        FaultKind::InvalidType {
            message: message.into(),
            received,
        }
    }

    /// An type mismatch occurred.
    ///
    /// These patterns will be replaced in `message` before being Displayed:
    ///
    /// - @expected
    /// - @received-value
    /// - @received-kind
    pub fn type_mismatch(message: impl Into<String>, expected: ValueKind, received: Value) -> Self {
        FaultKind::TypeMismatch {
            message: message.into(),
            expected,
            received,
        }
    }

    /// Returns a [`FaultKind::Dynamic`].
    pub fn dynamic<T: Debug + Display + 'static>(fault: T) -> Self {
        Self::Dynamic(DynamicFault::new(fault))
    }
}

impl From<std::io::Error> for FaultKind {
    fn from(io_err: std::io::Error) -> Self {
        Self::Dynamic(DynamicFault::new(io_err))
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
            FaultKind::ArgumentMissing(missing) => write!(f, "missing argument `{missing}`"),
            FaultKind::TooManyArguments(extra) => write!(f, "unexpected argument `{extra}`"),
            FaultKind::ValueCannotBeHashed(value) => {
                write!(
                    f,
                    "value does not support hashing: `{value}` ({})",
                    value.kind()
                )
            }
            FaultKind::ValueOutOfRange(what) => write!(f, "`{what}` is out of valid range"),
        }
    }
}

/// A stack frame entry of a [`Fault`].
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct FaultStackFrame {
    /// The vtable index of the function being executed. If None, the
    /// instructions being executed were passed directly into
    /// [`VirtualMachine::run()`].
    pub vtable_index: Option<usize>,
    /// The index of the instruction that was executing when this fault was
    /// raised.
    pub instruction_index: usize,
}

/// A paused code execution.
#[derive(Debug, PartialEq)]
pub struct PausedExecution<'a, Env, ReturnType>
where
    Env: Environment,
{
    context: Option<&'a mut VirtualMachine<Env>>,
    operations: Option<Cow<'a, [Instruction<Env::Intrinsic>]>>,
    stack: VecDeque<PausedFrame>,
    _return: PhantomData<ReturnType>,
}

impl<'a, Env, ReturnType> PausedExecution<'a, Env, ReturnType>
where
    Env: Environment,
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

#[derive(Debug, Eq, PartialEq)]
struct PausedFrame {
    return_offset: usize,
    arg_offset: usize,
    variables_offset: usize,

    return_value: Option<Value>,
    vtable_index: Option<usize>,
    operation_index: usize,
    destination: Destination,
}

/// A type that can be constructed from popping from the virtual machine stack.
pub trait FromStack: Sized {
    /// Returns an instance constructing from the stack.
    fn from_value(value: Value) -> Result<Self, FaultKind>;
}

impl FromStack for Value {
    fn from_value(value: Value) -> Result<Self, FaultKind> {
        Ok(value)
    }
}

impl FromStack for i64 {
    fn from_value(value: Value) -> Result<Self, FaultKind> {
        match value {
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
    fn from_value(value: Value) -> Result<Self, FaultKind> {
        match value {
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
    fn from_value(value: Value) -> Result<Self, FaultKind> {
        match value {
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
    fn from_value(_value: Value) -> Result<Self, FaultKind> {
        Ok(())
    }
}

impl<T> FromStack for T
where
    T: DynamicValue + Clone,
{
    fn from_value(value: Value) -> Result<Self, FaultKind> {
        value.into_dynamic().map_err(|value| {
            FaultKind::type_mismatch(
                "invalid type",
                ValueKind::Dynamic(Symbol::from(type_name::<T>())),
                value,
            )
        })
    }
}

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

/// Customizes the behavior of a virtual machine instance.
pub trait Environment: 'static {
    /// The string type for this environment.
    type String: DynamicValue + for<'a> From<&'a str> + From<String>;

    /// The intrinsics offered by this environment.
    type Intrinsic: Clone + PartialEq + Display + Debug + FromStr;

    /// Evalutes the `intrinsic` operation with the provided arguments.
    ///
    /// This is invoked when the virtual machine executes an
    /// [`Instruction::CallIntrinsic`].
    fn intrinsic(
        &mut self,
        intrinsic: &Self::Intrinsic,
        args: PoppedValues<'_>,
    ) -> Result<Value, FaultKind>;

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

    /// Converts `value` to a custom type supported by the runtime.
    ///
    /// The provided implementation supports the `String` type.
    fn convert(&self, value: &Value, kind: &Symbol) -> Result<Value, FaultKind> {
        if kind == "String" {
            self.convert_string(value)
        } else {
            Err(FaultKind::invalid_type(
                format!("@received-kind cannot be converted to {kind}"),
                value.clone(),
            ))
        }
    }

    /// Converts `value` to a [`Value`] containing an instance of `Self::String`.
    ///
    /// The provided implementation supports the `String` type.
    fn convert_string(&self, value: &Value) -> Result<Value, FaultKind> {
        match value {
            Value::Void => return Ok(Value::dynamic(<Self::String as From<&str>>::from(""))),
            Value::Integer(value) => {
                return Ok(Value::dynamic(<Self::String as From<String>>::from(
                    value.to_string(),
                )))
            }
            Value::Real(value) => {
                return Ok(Value::dynamic(<Self::String as From<String>>::from(
                    value.to_string(),
                )))
            }
            Value::Boolean(value) => {
                return Ok(Value::dynamic(<Self::String as From<String>>::from(
                    value.to_string(),
                )))
            }
            Value::Dynamic(value) => {
                if let Some(value) = value.convert(&Symbol::from("String")) {
                    return Ok(value);
                }
            }
        }
        Err(FaultKind::invalid_type(
            "@received-kind cannot be converted to String",
            value.clone(),
        ))
    }
}

impl Environment for () {
    type String = String;
    type Intrinsic = Noop;

    fn intrinsic(
        &mut self,
        _intrinsic: &Self::Intrinsic,
        _args: PoppedValues<'_>,
    ) -> Result<Value, FaultKind> {
        Ok(Value::Void)
    }

    #[inline]
    fn step(&mut self) -> ExecutionBehavior {
        ExecutionBehavior::Continue
    }
}

/// An [`Environment`] that allows executing an amount of instructions before
/// pausing the virtual machine.
#[derive(Debug, Default)]
#[must_use]
pub struct Budgeted<Env> {
    /// The wrapped environment.
    pub env: Env,
    remaining_steps: usize,
}

impl Budgeted<()> {
    /// Returns a budgeted default environment.
    pub fn empty() -> Self {
        Self::new(0, ())
    }
}

impl<Env> Budgeted<Env> {
    /// Returns a new instance with the provided initial budget.
    pub const fn new(initial_budget: usize, env: Env) -> Self {
        Self {
            env,
            remaining_steps: initial_budget,
        }
    }

    /// Returns the current balance of the budget.
    #[must_use]
    pub const fn balance(&self) -> usize {
        self.remaining_steps
    }

    /// Returns the current balance of the budget.
    #[must_use]
    pub fn charge(&mut self) -> bool {
        if self.remaining_steps > 0 {
            self.remaining_steps -= 1;
            true
        } else {
            false
        }
    }

    /// Adds an additional budget. This value will saturate `usize` instead of
    /// panicking or overflowing.
    pub fn add_budget(&mut self, additional_budget: usize) {
        self.remaining_steps = self.remaining_steps.saturating_add(additional_budget);
    }
}

impl<Env> Environment for Budgeted<Env>
where
    Env: Environment,
{
    type String = Env::String;
    type Intrinsic = Env::Intrinsic;

    #[inline]
    fn step(&mut self) -> ExecutionBehavior {
        if self.charge() {
            self.env.step()
        } else {
            ExecutionBehavior::Pause
        }
    }

    fn intrinsic(
        &mut self,
        intrinsic: &Self::Intrinsic,
        args: PoppedValues<'_>,
    ) -> Result<Value, FaultKind> {
        self.env.intrinsic(intrinsic, args)
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
    let mut context = VirtualMachine::default_for(Budgeted::new(0, ()));
    let mut pause_count = 0;
    let mut fault = context
        .run::<i64>(
            Cow::Borrowed(&[
                Instruction::Add {
                    left: ValueOrSource::Value(Value::Integer(1)),
                    right: ValueOrSource::Value(Value::Integer(2)),
                    destination: Destination::Variable(0),
                },
                Instruction::Add {
                    left: ValueOrSource::Variable(0),
                    right: ValueOrSource::Value(Value::Integer(3)),
                    destination: Destination::Variable(0),
                },
                Instruction::Add {
                    left: ValueOrSource::Variable(0),
                    right: ValueOrSource::Value(Value::Integer(4)),
                    destination: Destination::Return,
                },
            ]),
            1,
        )
        .unwrap_err();
    let output = loop {
        pause_count += 1;
        println!("Paused {pause_count}");
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

    assert_eq!(output, 10);
    assert_eq!(pause_count, 4); // Paused once at the start, then once per instruction.
}

#[test]
fn budget_with_frames() {
    let test = Function {
        name: Symbol::from("test"),
        arg_count: 1,
        variable_count: 2,
        code: vec![
            Instruction::If {
                condition: ValueOrSource::Argument(0),
                false_jump_to: 12,
            },
            Instruction::Load {
                variable_index: 0,
                value: ValueOrSource::Value(Value::Integer(1)),
            },
            Instruction::Push(ValueOrSource::Value(Value::Integer(1))),
            Instruction::Push(ValueOrSource::Value(Value::Integer(2))),
            Instruction::Add {
                left: ValueOrSource::Variable(0),
                right: ValueOrSource::Value(Value::Integer(2)),
                destination: Destination::Variable(0),
            },
            Instruction::Push(ValueOrSource::Value(Value::Integer(3))),
            Instruction::Add {
                left: ValueOrSource::Variable(0),
                right: ValueOrSource::Value(Value::Integer(3)),
                destination: Destination::Variable(0),
            },
            Instruction::Push(ValueOrSource::Value(Value::Integer(4))),
            Instruction::Add {
                left: ValueOrSource::Variable(0),
                right: ValueOrSource::Value(Value::Integer(4)),
                destination: Destination::Variable(0),
            },
            Instruction::Push(ValueOrSource::Value(Value::Integer(5))),
            Instruction::Add {
                left: ValueOrSource::Variable(0),
                right: ValueOrSource::Value(Value::Integer(5)),
                destination: Destination::Variable(0),
            },
            Instruction::Return(Some(ValueOrSource::Variable(0))),
            // If we were passed false, call ourself twice.
            Instruction::Push(ValueOrSource::Value(Value::Boolean(true))),
            Instruction::Call {
                vtable_index: None,
                arg_count: 1,
                destination: Destination::Variable(0),
            },
            Instruction::Push(ValueOrSource::Value(Value::Boolean(true))),
            Instruction::Call {
                vtable_index: None,
                arg_count: 1,
                destination: Destination::Variable(1),
            },
            Instruction::Add {
                left: ValueOrSource::Variable(0),
                right: ValueOrSource::Variable(1),
                destination: Destination::Variable(0),
            }, // should produce 30
            Instruction::Push(ValueOrSource::Variable(0)),
        ],
    };
    let mut context = VirtualMachine::default_for(Budgeted::new(0, ())).with_function(test);
    let mut fault = context
        .run::<i64>(
            Cow::Borrowed(&[
                Instruction::Push(ValueOrSource::Value(Value::Boolean(false))),
                Instruction::Call {
                    vtable_index: Some(0),
                    arg_count: 1,
                    destination: Destination::Stack,
                },
            ]),
            0,
        )
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

/// A block of code that can be executed on the virtual machine.
#[derive(Debug)]
pub struct CodeBlock<Intrinsic> {
    /// The number of variables this code block requires.
    pub variables: usize,

    /// The virtual machine instructions.
    pub code: Vec<Instruction<Intrinsic>>,
}

impl<Intrinsic> CodeBlock<Intrinsic> {
    /// Returns a [`Display`] implementor that indents each printed operation
    /// with `indentation`.
    #[must_use]
    pub fn display_indented<'a>(&'a self, indentation: &'a str) -> CodeBlockDisplay<'a, Intrinsic> {
        CodeBlockDisplay {
            block: self,
            indentation,
        }
    }
}

/// Displays a [`CodeBlock`] with optional indentation.
pub struct CodeBlockDisplay<'a, Intrinsic> {
    block: &'a CodeBlock<Intrinsic>,
    indentation: &'a str,
}

impl<'a, Intrinsic> Display for CodeBlockDisplay<'a, Intrinsic>
where
    Intrinsic: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut is_first = true;
        for i in &self.block.code {
            if is_first {
                is_first = false;
            } else {
                f.write_char('\n')?;
            }
            f.write_str(self.indentation)?;
            Display::fmt(i, f)?;
        }
        Ok(())
    }
}

impl<Intrinsic> Display for CodeBlock<Intrinsic>
where
    Intrinsic: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(
            &CodeBlockDisplay {
                block: self,
                indentation: "",
            },
            f,
        )
    }
}

/// A stack of [`Value`]s.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Stack {
    values: Vec<Value>,
    length: usize,
    remaining_capacity: usize,
}

impl Default for Stack {
    fn default() -> Self {
        Self {
            values: Vec::default(),
            length: 0,
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
            length: 0,
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
            if self.length < self.values.len() {
                self.values[self.length] = value;
            } else {
                self.values.push(value);
            }
            self.length += 1;
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
        let mut args = args.into_iter().rev();
        let arg_count = args.len();
        if self.remaining_capacity >= arg_count {
            self.remaining_capacity -= arg_count;
            let new_length = self.length + arg_count;
            let current_vec_length = self.values.len();
            if new_length < current_vec_length {
                // We can replace the existing values in this range
                self.values.splice(self.length..new_length, args);
            } else {
                while self.length < current_vec_length {
                    self.values[self.length] = args.next().expect("length checked");
                    self.length += 1;
                }
                // The remaining can be added to the end of the vec
                self.values.extend(args);
            }

            self.length = new_length;

            Ok(arg_count)
        } else {
            Err(FaultKind::StackOverflow)
        }
    }

    /// Pops `count` elements from the top of the stack.
    ///
    /// This iterator returns the values in the sequence that they are ordered
    /// on the stack, which is different than calling pop() `count` times
    /// sequentially. For example, if the stack contains `[0, 1, 2, 3]`, calling
    /// pop() twice will result in `3, 2`. Calling `pop_n(2)` will result in `2,
    /// 3`.
    pub fn pop_n(&mut self, count: usize) -> PoppedValues<'_> {
        // Make sure we aren't trying to pop too many
        let end = self.length;
        let count = count.min(end);
        let start = end - count;
        self.remaining_capacity += count;
        self.length -= count;
        PoppedValues {
            stack: self,
            current: start,
            end,
        }
    }

    /// Returns a reference to the top [`Value`] on the stack, or returns a
    /// [`FaultKind::StackUnderflow`] if no values are present.
    #[inline]
    pub fn top(&self) -> Result<&Value, FaultKind> {
        if self.length > 0 {
            Ok(&self.values[self.length])
        } else {
            Err(FaultKind::StackUnderflow)
        }
    }

    /// Returns a reference to the top [`Value`] on the stack, or returns a
    /// [`FaultKind::StackUnderflow`] if no values are present.
    #[inline]
    pub fn top_mut(&mut self) -> Result<&mut Value, FaultKind> {
        if self.length > 0 {
            Ok(&mut self.values[self.length - 1])
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
        if let Some(new_length) = self.length.checked_sub(1) {
            let value = std::mem::take(&mut self.values[new_length]);
            self.remaining_capacity += 1;
            self.length = new_length;
            Ok(value)
        } else {
            Err(FaultKind::StackUnderflow)
        }
    }

    /// Truncates the stack to `new_length`. If the `new_length` is larger than
    /// the current length, this function does nothing.
    pub fn truncate(&mut self, new_length: usize) {
        let values_to_remove = self.length.checked_sub(new_length);
        match values_to_remove {
            Some(values_to_remove) if values_to_remove > 0 => {
                self.pop_n(values_to_remove);
            }
            _ => {}
        }
    }

    /// Returns the number of [`Value`]s contained in this stack.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.length
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
        let mut start = match range.start_bound() {
            Bound::Included(start) => *start,
            Bound::Excluded(start) => start.saturating_sub(1),
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(end) => end.saturating_add(1),
            Bound::Excluded(end) => *end,
            Bound::Unbounded => self.length,
        };
        let removed = end - start;
        if removed > 0 {
            if let Some(values_to_copy) = self.length.checked_sub(end) {
                // We have values at the end we should copy first
                for index in 0..values_to_copy {
                    let value = std::mem::take(&mut self.values[end + index]);
                    self.values[start + index] = value;
                }
                start += values_to_copy;
            }
            // Replace the values with Void to free any ref-counted values.
            if end > start {
                // For some odd reason, fill_with is faster than fill here.
                self.values[start..end].fill_with(|| Value::Void);
            }
        }
        self.remaining_capacity += removed;
        self.length -= removed;
    }

    // fn clear(&mut self) {
    //     if self.length > 0 {
    //         self.values[0..self.length].fill_with(|| Value::Void);
    //     }
    //     self.remaining_capacity += self.length;
    //     self.length = 0;
    // }

    #[inline]
    fn grow_to(&mut self, new_size: usize) -> Result<(), FaultKind> {
        let extra_capacity = new_size.saturating_sub(self.length);
        if let Some(remaining_capacity) = self.remaining_capacity.checked_sub(extra_capacity) {
            self.remaining_capacity = remaining_capacity;
            if new_size >= self.values.len() {
                self.values.resize_with(new_size, || Value::Void);
            }
            self.length = new_size;
            Ok(())
        } else {
            Err(FaultKind::StackOverflow)
        }
    }

    /// Grows the stack by `additional_voids`, inserting [`Value::Void`] to fill
    /// in any newly allocated space.
    #[inline]
    pub fn grow_by(&mut self, additional_voids: usize) -> Result<(), FaultKind> {
        if let Some(remaining_capacity) = self.remaining_capacity.checked_sub(additional_voids) {
            self.remaining_capacity = remaining_capacity;
            let new_size = self.length + additional_voids;
            if new_size > self.values.len() {
                self.values.resize_with(new_size, || Value::Void);
            }
            self.length = new_size;
            Ok(())
        } else {
            Err(FaultKind::StackOverflow)
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

/// An iterator over a sequence of values being removed from the top of a
/// [`Stack`].
///
/// This iterator returns the values in the sequence that they are ordered on
/// the stack, which is different than calling pop() `count` times sequentially.
/// For example, if the stack contains `[0, 1, 2, 3]`, calling pop() twice will
/// result in `3, 2`. Calling `pop_n(2)` will result in `2, 3`.
pub struct PoppedValues<'a> {
    stack: &'a mut Stack,
    end: usize,
    current: usize,
}

impl<'a> PoppedValues<'a> {
    /// Returns the next value or returns a [`FaultKind::ArgumentMissing`] if no
    /// more parameters are found.
    pub fn next_argument(&mut self, name: &str) -> Result<Value, FaultKind> {
        self.next()
            .ok_or_else(|| FaultKind::ArgumentMissing(Symbol::from(name)))
    }

    /// Checks if all values have been iterated. If not,
    /// [`FaultKind::TooManyArguments`] will be returned.
    pub fn verify_empty(&mut self) -> Result<(), FaultKind> {
        if let Some(extra) = self.next() {
            Err(FaultKind::TooManyArguments(extra))
        } else {
            Ok(())
        }
    }
}

impl<'a> Drop for PoppedValues<'a> {
    fn drop(&mut self) {
        self.stack.values[self.current..self.end].fill_with(|| Value::Void);
    }
}

impl<'a> Iterator for PoppedValues<'a> {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.end {
            let result = Some(std::mem::take(&mut self.stack.values[self.current]));
            self.current += 1;
            result
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.end - self.current;
        (remaining, Some(remaining))
    }
}

impl<'a> ExactSizeIterator for PoppedValues<'a> {}

/// A [`Fault`] that arose from a [`Dynamic`] value.
#[derive(Debug, Clone)]
pub struct DynamicFault(Arc<dyn AnyDynamicError>);

impl PartialEq for DynamicFault {
    fn eq(&self, other: &Self) -> bool {
        self.0.data_ptr() == other.0.data_ptr()
    }
}

impl DynamicFault {
    /// Returns a new instance containing the provided error.
    pub fn new<T: Debug + Display + 'static>(error: T) -> Self {
        Self(Arc::new(DynamicErrorContents(Some(error))))
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
        if let Some(opt_any) = Arc::get_mut(&mut self.0)
            .and_then(|arc| arc.as_opt_any_mut().downcast_mut::<Option<T>>())
        {
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

    #[doc(hidden)]
    fn data_ptr(&self) -> *const u8;
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

    fn data_ptr(&self) -> *const u8 {
        (self as *const Self).cast::<u8>()
    }
}

#[test]
fn invalid_variables() {
    let test = Function {
        name: Symbol::from("test"),
        arg_count: 0,
        variable_count: 0,
        code: vec![Instruction::Push(ValueOrSource::Variable(0))],
    };
    let mut context = VirtualMachine::empty().with_function(test);
    assert!(matches!(
        context
            .run::<i64>(
                Cow::Borrowed(&[Instruction::Call {
                    vtable_index: Some(0),
                    arg_count: 0,
                    destination: Destination::Stack,
                }],),
                0
            )
            .unwrap_err()
            .kind,
        FaultOrPause::Fault(FaultKind::InvalidVariableIndex)
    ));
}

#[test]
fn invalid_argument() {
    let test = Function {
        name: Symbol::from("test"),
        arg_count: 0,
        variable_count: 0,
        code: vec![Instruction::Push(ValueOrSource::Argument(0))],
    };
    let mut context = VirtualMachine::empty().with_function(test);
    assert!(matches!(
        context
            .run::<i64>(
                Cow::Borrowed(&[Instruction::Call {
                    vtable_index: Some(0),
                    arg_count: 0,
                    destination: Destination::Stack,
                }]),
                0
            )
            .unwrap_err()
            .kind,
        FaultOrPause::Fault(FaultKind::InvalidArgumentIndex)
    ));
}

#[test]
fn invalid_vtable_index() {
    let mut context = VirtualMachine::empty();
    assert!(matches!(
        context
            .run::<i64>(
                Cow::Borrowed(&[Instruction::Call {
                    vtable_index: Some(0),
                    arg_count: 0,
                    destination: Destination::Stack,
                }]),
                0
            )
            .unwrap_err()
            .kind,
        FaultOrPause::Fault(FaultKind::InvalidVtableIndex)
    ));
}

#[test]
fn function_without_return_value() {
    let test = Function {
        name: Symbol::from("test"),
        arg_count: 0,
        variable_count: 0,
        code: vec![],
    };
    let mut context = VirtualMachine::empty().with_function(test);
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
        name: Symbol::from("test"),
        arg_count: 0,
        variable_count: 0,
        code: vec![
            Instruction::Push(ValueOrSource::Value(Value::Integer(1))),
            Instruction::Push(ValueOrSource::Value(Value::Integer(2))),
        ],
    };
    let mut context = VirtualMachine::empty().with_function(test);
    assert_eq!(
        context
            .run::<Value>(
                Cow::Borrowed(&[Instruction::Call {
                    vtable_index: Some(0),
                    arg_count: 0,
                    destination: Destination::Stack,
                }]),
                0
            )
            .unwrap(),
        Value::Integer(1)
    );

    assert!(context.stack.is_empty());
}

/// All errors that can be encountered executing Bud code.
#[derive(Debug, PartialEq)]
pub enum Error<'a, Env, ReturnType>
where
    Env: Environment,
{
    /// An error occurred while linking an [`Module`](ir::Module).
    Link(ir::LinkError),
    /// A fault occurred while running the virtual machine.
    Fault(Fault<'a, Env, ReturnType>),
}

impl<Env, ReturnType> Clone for Error<'static, Env, ReturnType>
where
    Env: Environment,
{
    fn clone(&self) -> Self {
        match self {
            Self::Link(arg0) => Self::Link(arg0.clone()),
            Self::Fault(arg0) => Self::Fault(arg0.clone()),
        }
    }
}

impl<'a, Env, ReturnType> Error<'a, Env, ReturnType>
where
    Env: Environment,
{
    /// Asserts that this error does not contain a paused execution. Returns an
    /// [`Error`] instance with a `'static` lifetime.
    ///
    /// # Panics
    ///
    /// If this contains [`Error::Fault`] with a kind of
    /// [`FaultOrPause::Pause`], this function will panic. Paused execution
    /// mutably borrows the virtual machine's state.
    #[must_use]
    pub fn expect_no_pause(self) -> Error<'static, Env, ReturnType> {
        match self {
            Error::Link(compilation) => Error::Link(compilation),
            Error::Fault(Fault {
                kind: FaultOrPause::Fault(fault),
                stack,
            }) => Error::Fault(Fault {
                kind: FaultOrPause::Fault(fault),
                stack,
            }),
            Error::Fault(_) => unreachable!("paused execution"),
        }
    }
}

impl<'a, Env, ReturnType> std::error::Error for Error<'a, Env, ReturnType>
where
    Env: std::fmt::Debug + Environment,
    ReturnType: std::fmt::Debug,
{
}

impl<'a, Env, ReturnType> Display for Error<'a, Env, ReturnType>
where
    Env: Environment,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Link(err) => write!(f, "link error: {err}"),
            Error::Fault(err) => write!(f, "vm fault: {err}"),
        }
    }
}
impl<'a, Env, ReturnType> From<ir::LinkError> for Error<'a, Env, ReturnType>
where
    Env: Environment,
{
    fn from(err: ir::LinkError) -> Self {
        Self::Link(err)
    }
}

impl<'a, Env, ReturnType> From<Fault<'a, Env, ReturnType>> for Error<'a, Env, ReturnType>
where
    Env: Environment,
{
    fn from(fault: Fault<'a, Env, ReturnType>) -> Self {
        Self::Fault(fault)
    }
}

impl<'a, Env, ReturnType> From<FaultKind> for Error<'a, Env, ReturnType>
where
    Env: Environment,
{
    fn from(fault: FaultKind) -> Self {
        Self::Fault(Fault::from(fault))
    }
}

/// An intrinsic that does nothing.
///
/// This type can be used for [`Environment::Intrinsic`] if there is no need for
/// custom intrinsics.
#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub struct Noop;

impl FromStr for Noop {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "noop" {
            Ok(Self)
        } else {
            Err(())
        }
    }
}

impl Display for Noop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("noop")
    }
}
