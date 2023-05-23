use std::{
    borrow::Borrow,
    collections::HashSet,
    fmt::Display,
    hash::Hash,
    ops::Deref,
    sync::{
        atomic::{self, AtomicBool},
        Arc, Mutex,
    },
};

static ACTIVE_SYMBOLS: Mutex<Option<Symbols>> = Mutex::new(None);

fn with_active_symbols<T>(logic: impl FnOnce(&mut Symbols) -> T) -> T {
    let mut symbols = ACTIVE_SYMBOLS.lock().expect("poisoned");
    if symbols.is_none() {
        *symbols = Some(Symbols {
            active: HashSet::new(),
            slots: Vec::new(),
            free_slots: Vec::new(),
        });
    }

    logic(symbols.as_mut().expect("always initialized"))
}

struct Symbols {
    active: HashSet<SharedData>,
    slots: Vec<Option<Symbol>>,
    free_slots: Vec<usize>,
}

/// A String-like type that ensures only one instance of each Symbol exists per
/// value, enabling quicker lookups by not requiring string comparisons.
///
/// After all instances of a given Symbol are dropped, the underlying storage is
/// released.
///
/// This type's [`Hash`] implementation is different than `String`'s hash
/// implementation. This type avoids implementing `Borrow<str>` to prevent using
/// strings to look up values in `HashMap`s/`HashSet`s where this type is used
/// as the key.
#[derive(Debug, Clone)]
pub struct Symbol(SharedData);

impl Symbol {
    /// Returns this symbol's underlying representation.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0 .0.value
    }
}

impl Hash for Symbol {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0 .0.index.hash(state);
    }
}

impl Eq for Symbol {}

impl PartialEq for Symbol {
    fn eq(&self, other: &Self) -> bool {
        self.0 .0.index == other.0 .0.index
    }
}

impl From<&Symbol> for Symbol {
    fn from(value: &Symbol) -> Self {
        value.clone()
    }
}

#[derive(Debug, Clone)]
struct SharedData(Arc<Data>);

#[derive(Debug)]
struct Data {
    index: usize,
    value: String,
    freeing: AtomicBool,
}

impl Hash for SharedData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.value.hash(state);
    }
}

impl Eq for SharedData {}

impl PartialEq for SharedData {
    fn eq(&self, other: &Self) -> bool {
        self.0.index == other.0.index
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self)
    }
}

impl Borrow<str> for SharedData {
    fn borrow(&self) -> &str {
        &self.0.value
    }
}

impl<'a> From<&'a str> for Symbol {
    fn from(sym: &'a str) -> Self {
        with_active_symbols(|symbols| {
            if let Some(symbol) = symbols.active.get(sym).cloned() {
                Symbol(symbol)
            } else {
                let value = sym.to_string();

                let index = if let Some(free_slot) = symbols.free_slots.pop() {
                    free_slot
                } else {
                    let slot_id = symbols.slots.len();
                    symbols.slots.push(None);
                    slot_id
                };

                let symbol = Symbol(SharedData(Arc::new(Data {
                    index,
                    value,
                    freeing: AtomicBool::new(false),
                })));
                symbols.active.insert(symbol.0.clone());
                symbols.slots[index] = Some(symbol.clone());
                symbol
            }
        })
    }
}

impl Deref for Symbol {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0 .0.value
    }
}

impl PartialEq<str> for Symbol {
    fn eq(&self, other: &str) -> bool {
        &**self == other
    }
}

impl<'a> PartialEq<&'a str> for Symbol {
    fn eq(&self, other: &&'a str) -> bool {
        self == *other
    }
}

impl Drop for SharedData {
    fn drop(&mut self) {
        // The main Symbols structure holds two strong references to the same
        // Arc we hold. Thus, if we reach 3 strong count (our ref included), we
        // need to remove the symbol so it can be freeed.
        //
        // We can use any form of atomics here because if the strong count is 3,
        // we can be guaranteed the only thread able to free our data is this
        // thread.
        if Arc::strong_count(&self.0) == 3
            && self
                .0
                .freeing
                .compare_exchange(
                    false,
                    true,
                    atomic::Ordering::Relaxed,
                    atomic::Ordering::Relaxed,
                )
                .is_ok()
        {
            with_active_symbols(|symbols| {
                // Check that the strong count hasn't changed. If it has, we
                // need to allow the symbol to stay alive.
                if Arc::strong_count(&self.0) > 3 {
                    self.0.freeing.store(false, atomic::Ordering::Relaxed);
                } else {
                    symbols.active.remove(self);
                    symbols.slots[self.0.index] = None;
                    symbols.free_slots.push(self.0.index);
                }
            });
        }
    }
}

#[test]
fn basics() {
    let first_symbol = Symbol::from("basics-test-symbol");
    let slot = first_symbol.0 .0.index;
    let first_again = Symbol::from("basics-test-symbol");
    assert_eq!(slot, first_again.0 .0.index);
    assert_eq!(first_symbol, first_again);
    drop(first_again);
    // Dropping the second copy shouldn't free the underlying symbol
    with_active_symbols(|symbols| {
        assert!(symbols.active.contains("basics-test-symbol"));
        assert!(!symbols.slots.is_empty());
        assert!(symbols.slots[slot].is_some());
        assert!(!symbols.free_slots.iter().any(|free| *free == slot));
    });
    drop(first_symbol);
    with_active_symbols(|symbols| {
        assert!(!symbols.active.contains("basics-test-symbol"));
        match &symbols.slots[slot] {
            Some(new_symbol) => {
                // This test isn't run in isolation, so other symbols may get
                // registered between the drop and this block. Very unlikely,
                // but possible.
                assert_ne!(new_symbol, "basics-test-symbol");
            }
            None => {
                assert!(symbols.free_slots.iter().any(|free| *free == slot));
            }
        }
    });
}
