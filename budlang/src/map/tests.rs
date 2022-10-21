use std::{
    collections::{hash_map::RandomState, HashSet},
    hash::{BuildHasher, Hasher},
    time::{SystemTime, UNIX_EPOCH},
};

use crate::map::BudMap;

/// This hash implementor is designed to cause collisions by being a terrible
/// algorithm (only xor) and restricting the hash space to 8 bits. This means
/// any collection using this hasher will be *guaranteed* to have collisions
/// after 256 entries.
#[derive(Clone, Copy)]
struct BadHasher(u8);

impl Hasher for BadHasher {
    fn finish(&self) -> u64 {
        u64::from(self.0)
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= *byte;
        }
    }
}

/// A simple LCG RNG.
struct DebugRng(u32);

impl DebugRng {
    pub fn seed_from_time() -> Self {
        let time = SystemTime::now();
        Self::new(
            time.duration_since(UNIX_EPOCH)
                .expect("invalid sytem time")
                .subsec_nanos(),
        )
    }

    pub fn new(seed: u32) -> Self {
        println!("DebugRng Seed: {seed}");
        Self(seed)
    }

    pub fn next(&mut self) -> u32 {
        self.0 = self.0.wrapping_mul(16807).wrapping_add(1) % u32::MAX;
        self.0
    }
}

#[test]
fn ordered_map_test() {
    let mut map = BudMap::default();
    map.insert(1, 1);
    map.insert(4, 2);
    map.insert(2, 3);
    map.insert(3, 4);
    map.insert(5, 5);
    assert_eq!(map.get_by_index(0), Some(&1));
    assert_eq!(map.get_by_index(1), Some(&2));
    assert_eq!(map.get_by_index(2), Some(&3));
    assert_eq!(map.get_by_index(3), Some(&4));
    assert_eq!(map.get_by_index(4), Some(&5));
    let mut iter = map.iter();
    assert_eq!(iter.next(), Some((&1, &1)));
    assert_eq!(iter.next(), Some((&4, &2)));
    assert_eq!(iter.next(), Some((&2, &3)));
    assert_eq!(iter.next(), Some((&3, &4)));
    assert_eq!(iter.next(), Some((&5, &5)));
    assert!(iter.next().is_none());

    assert_eq!(map.remove(&2), Some(3));
    assert_eq!(map.get_by_index(0), Some(&1));
    assert_eq!(map.get_by_index(1), Some(&2));
    assert_eq!(map.get_by_index(2), Some(&5));
    assert_eq!(map.get_by_index(3), Some(&4));
    assert_eq!(map.get_by_index(4), None);
    let mut iter = map.iter();
    assert_eq!(iter.next(), Some((&1, &1)));
    assert_eq!(iter.next(), Some((&4, &2)));
    assert_eq!(iter.next(), Some((&5, &5)));
    assert_eq!(iter.next(), Some((&3, &4)));
    assert!(iter.next().is_none());
}

impl BuildHasher for BadHasher {
    type Hasher = Self;

    fn build_hasher(&self) -> Self::Hasher {
        *self
    }
}

fn rebin<Hasher: BuildHasher>(hasher: Hasher) {
    let mut map = BudMap::with_hasher(hasher);
    for i in 0..1000 {
        map.insert(i, i);
    }

    // Test getting by key
    for i in 0..1000 {
        assert_eq!(map.get(&i), Some(&i));
    }

    for i in 0..1000 {
        assert_eq!(map.get_by_index(i), Some(&i));
    }
}

#[test]
fn rebin_std_hasher() {
    rebin(RandomState::default());
}

#[test]
fn rebin_bad_hasher() {
    rebin(BadHasher(0));
}

fn insert_or_remove<Hasher: BuildHasher>(
    rng: &mut DebugRng,
    map: &mut BudMap<u32, u32, Hasher>,
    expected_entries: &mut Vec<(u32, u32)>,
    insert_weight: u32,
    removal_weight: u32,
) {
    let total_weight = insert_weight + removal_weight;
    if rng.next() % total_weight < removal_weight && !expected_entries.is_empty() {
        // Remove an element the same way the implementation does
        let index_to_remove = (rng.next() as usize) % expected_entries.len();
        let mut removed_entry = expected_entries.pop().expect("map was empty");
        if index_to_remove < expected_entries.len() {
            std::mem::swap(&mut expected_entries[index_to_remove], &mut removed_entry);
        }
        println!("Removed {}: {}", removed_entry.0, removed_entry.1);
        assert_eq!(
            map.remove(&removed_entry.0).expect("key not found"),
            removed_entry.1
        );
    } else {
        // Add an element 2963 2948
        let key = rng.next();
        let value = rng.next();

        let removed_value = if let Some((_, entry_value)) = expected_entries
            .iter_mut()
            .find(|(entry_key, _)| entry_key == &key)
        {
            println!("Replacing {} with {}", key, value);
            let old_value = *entry_value;
            *entry_value = value;
            Some(old_value)
        } else {
            println!("Inserting {}: {}", key, value);
            expected_entries.push((key, value));
            None
        };

        assert_eq!(map.insert(key, value), removed_value);
    }
}
fn verify_contents<Hasher: BuildHasher>(
    map: &BudMap<u32, u32, Hasher>,
    expected_entries: &Vec<(u32, u32)>,
) {
    // Verify once by iteration and once by key lookups.
    assert_eq!(map.len(), expected_entries.len());

    for (map_entry, vec_entry) in map.iter().zip(expected_entries.iter()) {
        assert_eq!(map_entry.0, &vec_entry.0);
        assert_eq!(map_entry.1, &vec_entry.1);
    }

    for (expected_key, expected_value) in expected_entries {
        assert_eq!(
            map.get(expected_key),
            Some(expected_value),
            "{expected_key} did not match expectations"
        );
    }

    let mut bins_pointed_to = HashSet::new();
    let mut bins_with_data = HashSet::new();
    for (bin_index, bin) in map.bins.iter().enumerate() {
        if bin.entry_index.as_opt().is_some() {
            assert!(bins_with_data.insert(bin_index));
            if let Some(collision_index) = bin.collision_index.as_opt() {
                assert!(bins_pointed_to.insert(collision_index));
            }
        }
    }
    let bad_bins = bins_pointed_to.difference(&bins_with_data);
    for bin in bad_bins {
        panic!("{bin}");
    }
}

fn random_build_and_drain<Hasher: BuildHasher>(hasher: Hasher, maximum_size: usize) {
    let mut expected_entries: Vec<(u32, u32)> = Vec::new();
    let mut map = BudMap::with_capacity_and_hasher(1, hasher);
    let mut rng = DebugRng::seed_from_time();

    // Build the map up to 10,000 entries, using a variable amount of chance for
    // removals.
    let desired_weight = rng.next() % 8 + 10;
    let opposite_weight = rng.next() % 5 + 2;
    while map.len() < maximum_size {
        insert_or_remove(
            &mut rng,
            &mut map,
            &mut expected_entries,
            desired_weight,
            opposite_weight,
        );

        verify_contents(&map, &expected_entries);
    }

    // Now do the reverse
    while !map.is_empty() {
        insert_or_remove(
            &mut rng,
            &mut map,
            &mut expected_entries,
            opposite_weight,
            desired_weight,
        );

        verify_contents(&map, &expected_entries);
    }
}

#[test]
fn random_build_and_drain_bad_hasher() {
    // miri runs out of memory in CI when run with too large of a data set. Give
    // that this map has no unsafe code, we could just ignore the tests but it
    // seems better to just reduce the count.
    #[cfg(miri)]
    const COUNT: usize = 300;
    #[cfg(not(miri))]
    const COUNT: usize = 3_000;
    random_build_and_drain(BadHasher(0), COUNT);
}

#[test]
fn random_build_and_drain_std_hasher() {
    // miri runs out of memory in CI when run with too large of a data set. Give
    // that this map has no unsafe code, we could just ignore the tests but it
    // seems better to just reduce the count.
    #[cfg(miri)]
    const COUNT: usize = 500;
    #[cfg(not(miri))]
    const COUNT: usize = 5_000;
    random_build_and_drain(RandomState::default(), COUNT);
}
