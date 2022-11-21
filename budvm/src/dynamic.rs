use std::{
    any::{Any, TypeId},
    cmp::Ordering,
    fmt::{Debug, Display},
    hash::Hasher,
    sync::Arc,
};

use crate::{symbol::Symbol, FaultKind, PoppedValues, Value, ValueKind};

/// A type that can be used in the virtual machine using [`Value::dynamic`].
pub trait DynamicValue: Send + Sync + Debug + 'static {
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

    /// Returns this value as an `i64`, if possible.
    ///
    /// Implementhing this function enables this type to be used in integer
    /// operations such as bitwise operations.
    #[must_use]
    fn as_i64(&self) -> Option<i64> {
        None
    }

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

    /// Attempts to compute the result adding self and other.
    ///
    /// While addition is normally an associative operation, `is_reverse` allows
    /// determining if `self` is the left operand or the right operand to the
    /// operation.
    ///
    /// If `is_reverse` is false, the operation being requested is `self` +
    /// `other`. If `is_reverse` is true, the operation being requested is
    /// `other` + `self`.
    #[allow(unused_variables)]
    fn checked_add(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        Ok(None)
    }

    /// Attempts to compute the result subtracting self and other.
    ///
    /// If `is_reverse` is false, the operation being requested is `self` -
    /// `other`. If `is_reverse` is true, the operation being requested is
    /// `other` - `self`.
    #[allow(unused_variables)]
    fn checked_sub(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        Ok(None)
    }

    /// Attempts to compute the result multiplying self and other.
    ///
    /// While multiplication is normally an associative operation, `is_reverse`
    /// allows
    /// determining if `self` is the left operand or the right operand to the
    /// operation.
    ///
    /// If `is_reverse` is false, the operation being requested is `self` *
    /// `other`. If `is_reverse` is true, the operation being requested is
    /// `other` * `self`.
    #[allow(unused_variables)]
    fn checked_mul(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        Ok(None)
    }

    /// Attempts to compute the result dividing self and other.
    ///
    /// If `is_reverse` is false, the operation being requested is `self` /
    /// `other`. If `is_reverse` is true, the operation being requested is
    /// `other` / `self`.
    #[allow(unused_variables)]
    fn checked_div(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        Ok(None)
    }

    /// Calls a function by `name` with `args`.
    #[allow(unused_variables)]
    fn call(&self, name: &Symbol, args: &mut PoppedValues<'_>) -> Result<Value, FaultKind> {
        Err(FaultKind::UnknownFunction {
            kind: ValueKind::Dynamic(self.kind()),
            name: name.clone(),
        })
    }

    /// Returns this value as represented in source, if possible.
    fn to_source(&self) -> Option<String> {
        None
    }

    /// Hashes the contents of this value. Returns true if this operation is
    /// supported.
    ///
    /// To allow the [`Value`] type to implement [`Hash`] but contain values
    /// that don't implement [`Hash`], this is not a trait that is required to
    /// implement.
    ///
    /// This allows safe collection types to be written, which check before key
    /// insertion that the value can be hashed and returns an error rather than
    /// panicking in the call to hash.
    #[allow(unused_variables)]
    fn hash<H>(&self, state: &mut H) -> bool
    where
        H: std::hash::Hasher,
    {
        false
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

impl Dynamic {
    /// Returns a new instance, wrapping `value`.
    ///
    /// This function causes two allocations: [`Arc::new()`] and [`Box::new()`].
    /// While `Arc<dyn T>` could be used for only one allocation, it uses a "fat
    /// pointer" which is double the size of a standard pointer. By using
    /// `Arc<Box<dyn T>>`, the `Box<dyn T>` becomes the fat pointer and the
    /// `Arc` remains a normal pointer. The net effect is that the [`Value`]
    /// enum is able to stay smaller due to this extra allocation.
    pub fn new<T: DynamicValue + 'static>(value: T) -> Self {
        Self(Arc::new(Box::new(DynamicValueData { value: Some(value) })))
    }

    /// Returns the result of [`DynamicValue::kind()`] for the wrapped value.
    #[must_use]
    pub fn kind(&self) -> &'static str {
        self.0.kind()
    }

    /// Returns the [`TypeId`] of the wrapped type.
    #[must_use]
    pub fn type_id(&self) -> TypeId {
        self.0.type_id()
    }

    /// Returns a reference to the contained value, if the contained type is
    /// `T`.
    #[must_use]
    pub fn inner<T: DynamicValue>(&self) -> Option<&T> {
        self.0.as_any().downcast_ref::<T>()
    }

    /// Attempts to unwrap the value. If there is more than one reference to
    /// this value, or `T` does not match the contained type, `Err(self)` will
    /// be returned.
    pub fn try_into_inner<T: DynamicValue>(self) -> Result<T, Self> {
        // Before we consume the value, verify we have the correct type.
        if self.inner::<T>().is_some() {
            // We can now destruct self safely without worrying about needing to
            // return an error.
            match Arc::try_unwrap(self.0) {
                Ok(mut boxed_value) => {
                    let opt_value = boxed_value
                        .as_opt_any_mut()
                        .downcast_mut::<Option<T>>()
                        .expect("type already checked");
                    let mut value = None;
                    std::mem::swap(opt_value, &mut value);
                    Ok(value.expect("value already taken"))
                }
                Err(arc_value) => Err(Self(arc_value)),
            }
        } else {
            Err(self)
        }
    }

    /// Returns the contained value if `T` is the contained type. If the value
    /// contains another type, `Err(self)` will be returned. Otherwise, the
    /// inner value will be returned.
    ///
    /// Because dynamic values are cheaply cloned by wrapping the value in an
    /// [`Arc`], this method will return a clone if there are any other
    /// instances that point to the same contained value. If this is the final
    /// instance of this value, the contained value will be returned without
    /// additional allocations.
    pub fn into_inner<T: DynamicValue + Clone>(self) -> Result<T, Self> {
        // Before we consume the value, verify we have the correct type.
        if self.inner::<T>().is_some() {
            // We can now destruct self safely without worrying about needing to
            // return an error.
            match Arc::try_unwrap(self.0) {
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

    /// Returns the result of [`DynamicValue::is_truthy()`] for the wrapped
    /// value.
    #[must_use]
    pub fn is_truthy(&self) -> bool {
        self.0.is_truthy()
    }

    /// Returns the result of [`DynamicValue::as_i64()`] for the wrapped value.
    #[must_use]
    pub fn as_i64(&self) -> Option<i64> {
        self.0.as_i64()
    }

    /// Returns the inverse of [`DynamicValue::is_truthy()`] for the wrapped
    /// value.
    #[must_use]
    pub fn is_falsey(&self) -> bool {
        !self.0.is_truthy()
    }

    /// Returns the result of [`DynamicValue::partial_eq()`] for the wrapped
    /// value.
    #[must_use]
    pub fn partial_eq(&self, other: &Value) -> Option<bool> {
        self.0.partial_eq(other)
    }

    /// Returns the result of [`DynamicValue::partial_cmp()`] for the wrapped
    /// value.
    #[must_use]
    pub fn partial_cmp(&self, other: &Value) -> Option<Ordering> {
        self.0.partial_cmp(other)
    }

    /// Returns the result of [`DynamicValue::checked_add()`] for the wrapped
    /// value.
    pub fn checked_add(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        self.0.checked_add(other, is_reverse)
    }

    /// Returns the result of [`DynamicValue::checked_sub()`] for the wrapped
    /// value.
    pub fn checked_sub(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        self.0.checked_sub(other, is_reverse)
    }

    /// Returns the result of [`DynamicValue::checked_mul()`] for the wrapped
    /// value.
    pub fn checked_mul(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        self.0.checked_mul(other, is_reverse)
    }

    /// Returns the result of [`DynamicValue::checked_div()`] for the wrapped
    /// value.
    pub fn checked_div(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        self.0.checked_div(other, is_reverse)
    }

    /// Invokes [`DynamicValue::call`] with the given parameters.
    pub fn call(&mut self, name: &Symbol, args: PoppedValues<'_>) -> Result<Value, FaultKind> {
        self.0.call(name, args)
    }

    /// Returns the result of [`DynamicValue::to_source()`] for the wrapped
    /// value.
    #[must_use]
    pub fn to_source(&self) -> Option<String> {
        self.0.to_source()
    }

    /// Returns the result of [`DynamicValue::hash()`] for the wrapped
    /// value.
    pub fn hash<H: Hasher>(&self, state: &mut H) -> bool {
        self.0.hash(state)
    }
}

impl Display for Dynamic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0.to_source() {
            Some(value) => f.write_str(&value),
            None => Ok(()),
        }
    }
}

trait UnboxableDynamicValue: Debug + Send + Sync {
    fn type_id(&self) -> TypeId;
    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
    fn as_opt_any_mut(&mut self) -> &mut dyn Any;

    fn is_truthy(&self) -> bool;
    fn as_i64(&self) -> Option<i64>;
    fn kind(&self) -> &'static str;
    fn partial_eq(&self, other: &Value) -> Option<bool>;
    fn partial_cmp(&self, other: &Value) -> Option<Ordering>;
    fn checked_add(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind>;
    fn checked_sub(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind>;
    fn checked_mul(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind>;
    fn checked_div(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind>;
    fn to_source(&self) -> Option<String>;
    fn hash(&self, state: &mut dyn Hasher) -> bool;
    fn call(&self, name: &Symbol, arguments: PoppedValues<'_>) -> Result<Value, FaultKind>;
}

#[derive(Clone)]
struct DynamicValueData<T> {
    value: Option<T>,
}

impl<T> DynamicValueData<T> {
    #[inline]
    fn value(&self) -> &T {
        self.value.as_ref().expect("value taken")
    }
    #[inline]
    fn value_mut(&mut self) -> &mut T {
        self.value.as_mut().expect("value taken")
    }
}

impl<T> UnboxableDynamicValue for DynamicValueData<T>
where
    T: DynamicValue + Any + Debug,
{
    fn as_any(&self) -> &dyn Any {
        self.value()
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self.value_mut()
    }

    fn as_opt_any_mut(&mut self) -> &mut dyn Any {
        &mut self.value
    }

    fn is_truthy(&self) -> bool {
        self.value().is_truthy()
    }

    fn as_i64(&self) -> Option<i64> {
        self.value().as_i64()
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

    fn to_source(&self) -> Option<String> {
        self.value().to_source()
    }

    fn checked_add(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        self.value().checked_add(other, is_reverse)
    }

    fn checked_sub(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        self.value().checked_sub(other, is_reverse)
    }

    fn checked_mul(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        self.value().checked_mul(other, is_reverse)
    }

    fn checked_div(&self, other: &Value, is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        self.value().checked_div(other, is_reverse)
    }

    fn hash(&self, mut state: &mut dyn Hasher) -> bool {
        self.value().hash(&mut state)
    }

    fn type_id(&self) -> TypeId {
        TypeId::of::<T>()
    }

    fn call(&self, name: &Symbol, mut arguments: PoppedValues<'_>) -> Result<Value, FaultKind> {
        self.value().call(name, &mut arguments)
    }
}

impl<T> Debug for DynamicValueData<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(value) = self.value.as_ref() {
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
        if let Some(value) = self.value.as_ref() {
            Display::fmt(value, f)
        } else {
            Ok(())
        }
    }
}

pub(super) fn cmp(left: &Value, left_dynamic: &Dynamic, right: &Value) -> Option<Ordering> {
    match left_dynamic.partial_cmp(right) {
        Some(ordering) => Some(ordering),
        None => match right {
            Value::Dynamic(right) => right.partial_cmp(left).map(Ordering::reverse),
            _ => None,
        },
    }
}
