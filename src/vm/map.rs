use std::{
    collections::hash_map::RandomState,
    fmt::Debug,
    hash::BuildHasher,
    sync::{Mutex, MutexGuard, PoisonError},
};

use crate::{
    symbol::Symbol,
    vm::{DynamicValue, Value},
};

use super::{FaultKind, PoppedValues};

/// A wrapper for [`std::collections::HashMap<Value,Value>`] that prevents using
/// a [`Value`] that does not support hashing by returning an error.
///
/// This type uses a [`Mutex`] for interior mutability.
pub struct HashMap<State = RandomState>(Mutex<std::collections::HashMap<Value, Value, State>>)
where
    State: BuildHasher;

impl Default for HashMap<RandomState> {
    fn default() -> Self {
        Self::new()
    }
}

impl<State> Clone for HashMap<State>
where
    State: Clone + BuildHasher,
{
    fn clone(&self) -> Self {
        Self(Mutex::new(self.map().clone()))
    }
}

impl<State> From<std::collections::HashMap<Value, Value, State>> for HashMap<State>
where
    State: BuildHasher,
{
    fn from(collection: std::collections::HashMap<Value, Value, State>) -> Self {
        Self(Mutex::new(collection))
    }
}

impl HashMap<RandomState> {
    /// Returns a new, empty hash map.
    ///
    /// Equivalent to [`std::collections::HashMap::new()`].
    #[must_use]
    pub fn new() -> Self {
        Self(Mutex::new(std::collections::HashMap::new()))
    }

    /// Returns a hash map that can contain at least `capacity` without
    /// reallocation.
    ///
    /// Equivalent to [`std::collections::HashMap::with_capacity()`].
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(Mutex::new(std::collections::HashMap::with_capacity(
            capacity,
        )))
    }
}

impl<State> HashMap<State>
where
    State: BuildHasher,
{
    /// Returns a new, empty hash map that uses `hash_builder` to initialize the
    /// hasher used for this map.
    ///
    /// Equivalent to [`std::collections::HashMap::with_hasher()`].
    #[must_use]
    pub fn with_hasher(hash_builder: State) -> Self {
        Self(Mutex::new(std::collections::HashMap::with_hasher(
            hash_builder,
        )))
    }

    /// Returns a hash map that can contain at least `capacity` without
    /// reallocation, using `hash_builder` to initialize the hasher used for
    /// this map.
    ///
    /// Equivalent to [`std::collections::HashMap::with_capacity_and_hasher()`].
    #[must_use]
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: State) -> Self {
        Self(Mutex::new(
            std::collections::HashMap::with_capacity_and_hasher(capacity, hash_builder),
        ))
    }

    fn map(&self) -> MutexGuard<'_, std::collections::HashMap<Value, Value, State>> {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Returns the number of items contained.
    pub fn len(&self) -> usize {
        self.map().len()
    }

    /// Returns true if this map contains no items.
    pub fn is_empty(&self) -> bool {
        self.map().is_empty()
    }

    /// Inserts a key-value pair into the map.
    ///
    /// Equivalent to [`std::collections::HashMap::insert()`], except this
    /// function checks that `key.implements_hash()` returns true. If it does
    /// not, [`FaultKind::ValueCannotBeHashed`] will be returned.
    pub fn insert(&self, k: Value, v: Value) -> Result<Option<Value>, FaultKind> {
        let mut map = self.map();
        Ok(map.insert(check_hashable(k)?, v))
    }

    /// Returns the value associated with `key`, if present.
    pub fn get(&self, key: &Value) -> Option<Value> {
        let map = self.map();
        map.get(key).cloned()
    }

    /// Removes the value associated with `key`, if present.
    pub fn remove(&self, key: &Value) -> Option<Value> {
        let mut map = self.map();
        map.remove(key)
    }

    /// Extracts the contained collection type.
    pub fn into_inner(self) -> std::collections::HashMap<Value, Value, State> {
        self.0.into_inner().unwrap_or_else(PoisonError::into_inner)
    }
}

impl<'a> TryFrom<PoppedValues<'a>> for HashMap<RandomState> {
    type Error = FaultKind;

    fn try_from(mut values: PoppedValues<'a>) -> Result<Self, Self::Error> {
        if values.len() & 1 == 1 {
            return Err(FaultKind::dynamic(
                "odd number of arguments passed to map constructor",
            ));
        }
        let mut map = std::collections::HashMap::with_capacity(values.len() / 2);

        while let Some(key) = values.next() {
            let value = values.next().expect("checked for odd length");

            map.insert(check_hashable(key)?, value);
        }

        Ok(Self::from(map))
    }
}

fn check_hashable(value: Value) -> Result<Value, FaultKind> {
    if value.implements_hash() {
        Ok(value)
    } else {
        Err(FaultKind::ValueCannotBeHashed(value))
    }
}

impl<State> Debug for HashMap<State>
where
    State: BuildHasher,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl<State> DynamicValue for HashMap<State>
where
    State: BuildHasher + Clone + Send + Sync + 'static,
{
    fn is_truthy(&self) -> bool {
        !self.map().is_empty()
    }

    fn kind(&self) -> &'static str {
        "Map"
    }

    fn partial_eq(&self, other: &Value) -> Option<bool> {
        if let Some(other) = other.as_dynamic::<Self>() {
            let lhs = self.map();
            let rhs = other.map();
            if lhs.len() == rhs.len() {
                for (lkey, lvalue) in lhs.iter() {
                    if rhs.get(lkey).map_or(true, |rvalue| lvalue != rvalue) {
                        return Some(false);
                    }
                }
                Some(true)
            } else {
                Some(false)
            }
        } else {
            None
        }
    }

    fn call(&self, name: &Symbol, args: &mut PoppedValues<'_>) -> Result<Value, FaultKind> {
        match name.as_str() {
            "count" => {
                args.verify_empty()?;
                let len = i64::try_from(self.map().len())
                    .map_err(|_| FaultKind::ValueOutOfRange("count"))?;
                Ok(Value::Integer(len))
            }
            "insert" => {
                let key = args
                    .next()
                    .ok_or_else(|| FaultKind::ArgumentMissing(Symbol::from("key")))?;
                let value = args
                    .next()
                    .ok_or_else(|| FaultKind::ArgumentMissing(Symbol::from("value")))?;
                args.verify_empty()?;

                let contained_value = self.insert(key, value)?.unwrap_or_default();

                Ok(contained_value)
            }
            "get" => {
                let key = args
                    .next()
                    .ok_or_else(|| FaultKind::ArgumentMissing(Symbol::from("key")))?;
                args.verify_empty()?;

                let contained_value = self.get(&key).unwrap_or_default();

                Ok(contained_value)
            }
            "remove" => {
                let key = args
                    .next()
                    .ok_or_else(|| FaultKind::ArgumentMissing(Symbol::from("key")))?;
                args.verify_empty()?;

                let contained_value = self.remove(&key).unwrap_or_default();

                Ok(contained_value)
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
}
