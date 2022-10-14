use std::{
    cmp::Ordering,
    collections::VecDeque,
    sync::{Mutex, MutexGuard, PoisonError},
};

use crate::{
    symbol::Symbol,
    vm::{DynamicValue, FaultKind, PoppedValues, Value},
};

/// A List type for Bud, which wraps a [`VecDeque<Value>`].
///
/// This type uses a [`Mutex`] for interior mutability, allowing lists to be
/// cheaply moved around by reference. Each interaction with this type locks the
/// Mutex.
///
/// [`VecDeque`] was chosen to allow users ultimate flexibility in
/// pushing/popping without worry about performance concerns.
#[derive(Debug)]
pub struct List(Mutex<VecDeque<Value>>);

impl Clone for List {
    fn clone(&self) -> Self {
        Self(Mutex::new(self.list().clone()))
    }
}

impl List {
    fn list(&self) -> MutexGuard<'_, VecDeque<Value>> {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Extracts the contained collection type.
    pub fn into_inner(self) -> VecDeque<Value> {
        self.0.into_inner().unwrap_or_else(PoisonError::into_inner)
    }

    /// Pushes `value` to the front of the list.
    pub fn push_front(&self, value: Value) {
        self.list().push_front(value);
    }

    /// Pushes `value` to the back of the list.
    pub fn push_back(&self, value: Value) {
        self.list().push_back(value);
    }

    /// Removes the first value in the list.
    pub fn pop_front(&self) -> Option<Value> {
        self.list().pop_front()
    }

    /// Removes the last value in the list.
    pub fn pop_back(&self) -> Option<Value> {
        self.list().pop_back()
    }

    /// Returns the number of values contained in the list.
    pub fn len(&self) -> usize {
        self.list().len()
    }

    /// Returns true if this list contains no values.
    pub fn is_empty(&self) -> bool {
        self.list().is_empty()
    }

    /// Returns the value contained at `index`, or `None` if `index` is outside
    /// of the bounds of this list.
    pub fn get(&self, index: usize) -> Option<Value> {
        self.list().get(index).cloned()
    }

    /// Removes the value contained at `index`, or `None` if `index` is outside
    /// of the bounds of this list.
    pub fn remove(&self, index: usize) -> Option<Value> {
        let mut list = self.list();
        list.remove(index)
    }
}

impl DynamicValue for List {
    fn is_truthy(&self) -> bool {
        !self.list().is_empty()
    }

    fn kind(&self) -> &'static str {
        "List"
    }

    fn partial_eq(&self, other: &Value) -> Option<bool> {
        let other = other.as_dynamic::<Self>()?;
        let lhs = self.list();
        let rhs = other.list();

        Some(*lhs == *rhs)
    }

    fn partial_cmp(&self, other: &Value) -> Option<Ordering> {
        let other = other.as_dynamic::<Self>()?;
        let other = other.list();
        let mut other = other.iter();

        let rhs = self.list();
        for lhs in rhs.iter() {
            let rhs = match other.next() {
                Some(rhs) => rhs,
                None => return Some(Ordering::Greater),
            };
            match lhs.partial_cmp(rhs) {
                Some(Ordering::Equal) => continue,
                non_equal => return non_equal,
            }
        }
        Some(if other.next().is_some() {
            Ordering::Less
        } else {
            Ordering::Equal
        })
    }

    fn call(&self, name: &Symbol, args: &mut PoppedValues<'_>) -> Result<Value, FaultKind> {
        match name.as_str() {
            "count" => {
                args.verify_empty()?;
                let len = i64::try_from(self.list().len())
                    .map_err(|_| FaultKind::ValueOutOfRange("count"))?;
                Ok(Value::Integer(len))
            }
            "push" => {
                let arg = args.next_argument("value")?;
                args.verify_empty()?;
                let mut list = self.list();
                list.push_back(arg.clone());
                Ok(arg)
            }
            "pop" => {
                args.verify_empty()?;
                let mut list = self.list();
                Ok(list.pop_back().unwrap_or_default())
            }
            "push_front" => {
                let arg = args.next_argument("value")?;
                args.verify_empty()?;
                let mut list = self.list();
                list.push_front(arg.clone());
                Ok(arg)
            }
            "pop_front" => {
                args.verify_empty()?;
                let mut list = self.list();
                Ok(list.pop_front().unwrap_or_default())
            }
            "remove" => {
                let index = args.next_argument("value")?;
                args.verify_empty()?;
                let index = index.as_i64().ok_or_else(|| {
                    FaultKind::invalid_type("index must be an integer", index.clone())
                })?;
                Ok(self
                    .remove(usize::try_from(index).unwrap_or(usize::MAX))
                    .unwrap_or_default())
            }
            _ => Err(FaultKind::UnknownFunction {
                kind: super::ValueKind::Dynamic(self.kind()),
                name: name.clone(),
            }),
        }
    }

    fn to_source(&self) -> Option<String> {
        None
    }

    fn hash<H>(&self, state: &mut H) -> bool
    where
        H: std::hash::Hasher,
    {
        let list = self.list();
        for value in list.iter() {
            if !value.try_hash(state) {
                return false;
            }
        }

        true
    }
}

impl FromIterator<Value> for List {
    fn from_iter<T: IntoIterator<Item = Value>>(iter: T) -> Self {
        Self(Mutex::new(VecDeque::from_iter(iter)))
    }
}
