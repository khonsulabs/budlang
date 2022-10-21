use std::{collections::HashMap, hash::BuildHasher};

use budlang::map::BudMap;
use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BatchSize, BenchmarkGroup, BenchmarkId,
    Criterion,
};
use indexmap::IndexMap;

trait Map<S>: Clone {
    fn label() -> &'static str;
    fn with_hasher(hasher: S) -> Self;
    fn insert(&mut self, key: u32, value: u32) -> Option<u32>;
    fn get(&self, key: &u32) -> Option<&u32>;
    fn remove(&mut self, key: &u32) -> Option<u32>;
}

impl<S> Map<S> for HashMap<u32, u32, S>
where
    S: BuildHasher + Clone,
{
    fn label() -> &'static str {
        "HashMap"
    }

    fn with_hasher(hasher: S) -> Self {
        Self::with_hasher(hasher)
    }

    fn insert(&mut self, key: u32, value: u32) -> Option<u32> {
        HashMap::insert(self, key, value)
    }

    fn get(&self, key: &u32) -> Option<&u32> {
        HashMap::get(self, key)
    }

    fn remove(&mut self, key: &u32) -> Option<u32> {
        HashMap::remove(self, key)
    }
}

impl<S> Map<S> for BudMap<u32, u32, S>
where
    S: BuildHasher + Clone,
{
    fn label() -> &'static str {
        "BudMap"
    }

    fn with_hasher(hasher: S) -> Self {
        Self::with_hasher(hasher)
    }

    fn insert(&mut self, key: u32, value: u32) -> Option<u32> {
        BudMap::insert(self, key, value)
    }

    fn get(&self, key: &u32) -> Option<&u32> {
        BudMap::get(self, key)
    }

    fn remove(&mut self, key: &u32) -> Option<u32> {
        BudMap::remove(self, key)
    }
}

impl<S> Map<S> for IndexMap<u32, u32, S>
where
    S: BuildHasher + Clone,
{
    fn label() -> &'static str {
        "IndexMap"
    }

    fn with_hasher(hasher: S) -> Self {
        Self::with_hasher(hasher)
    }

    fn insert(&mut self, key: u32, value: u32) -> Option<u32> {
        IndexMap::insert(self, key, value)
    }

    fn get(&self, key: &u32) -> Option<&u32> {
        IndexMap::get(self, key)
    }

    fn remove(&mut self, key: &u32) -> Option<u32> {
        IndexMap::remove(self, key)
    }
}

fn fill_entries<M: Map<fnv::FnvBuildHasher>>(
    state: fnv::FnvBuildHasher,
    count: usize,
    bench: &mut BenchmarkGroup<'_, WallTime>,
) {
    let rng = fastrand::Rng::with_seed(0);

    bench.bench_function(BenchmarkId::new(M::label(), count), |b| {
        b.iter(|| {
            let mut map = M::with_hasher(state.clone());
            for _ in 0..count {
                let key = rng.u32(..);
                let value = rng.u32(..);
                map.insert(key, value);
            }
        });
    });
}

fn bench_fills(
    state: &fnv::FnvBuildHasher,
    count: usize,
    bench: &mut BenchmarkGroup<'_, WallTime>,
) {
    fill_entries::<BudMap<u32, u32, fnv::FnvBuildHasher>>(state.clone(), count, bench);
    fill_entries::<HashMap<u32, u32, fnv::FnvBuildHasher>>(state.clone(), count, bench);
    fill_entries::<IndexMap<u32, u32, fnv::FnvBuildHasher>>(state.clone(), count, bench);
}

pub fn fills(c: &mut Criterion) {
    let state = fnv::FnvBuildHasher::default();
    let mut group = c.benchmark_group("fills");
    bench_fills(&state, 10, &mut group);
    bench_fills(&state, 100, &mut group);
    bench_fills(&state, 500, &mut group);
    bench_fills(&state, 1_000, &mut group);
    bench_fills(&state, 5_000, &mut group);
    bench_fills(&state, 10_000, &mut group);
    bench_fills(&state, 50_000, &mut group);
    bench_fills(&state, 100_000, &mut group);
    bench_fills(&state, 500_000, &mut group);
    bench_fills(&state, 1_000_000, &mut group);
}

fn remove_reinsert_entries<M: Map<fnv::FnvBuildHasher>>(
    state: fnv::FnvBuildHasher,
    count: usize,
    bench: &mut BenchmarkGroup<'_, WallTime>,
) {
    bench.bench_function(BenchmarkId::new(M::label(), count), |b| {
        let rng = fastrand::Rng::with_seed(0);
        let mut keys = Vec::with_capacity(count);
        let mut map = M::with_hasher(state.clone());

        for _ in 0..count {
            let key = rng.u32(..);
            let value = rng.u32(..);
            if map.insert(key, value).is_none() {
                keys.push(key);
            }
        }

        rng.shuffle(&mut keys);

        let mut key_index = 0;
        b.iter_batched(
            || {
                key_index += 1;
                if key_index == keys.len() {
                    key_index = 0;
                }
                key_index
            },
            |key_index| {
                let key = keys[key_index];
                let value = map.remove(&key).unwrap();
                map.insert(key, value);
            },
            BatchSize::LargeInput,
        );
    });
}

fn bench_remove_reinserts(
    state: &fnv::FnvBuildHasher,
    count: usize,
    bench: &mut BenchmarkGroup<'_, WallTime>,
) {
    remove_reinsert_entries::<BudMap<u32, u32, fnv::FnvBuildHasher>>(state.clone(), count, bench);
    remove_reinsert_entries::<HashMap<u32, u32, fnv::FnvBuildHasher>>(state.clone(), count, bench);
    remove_reinsert_entries::<IndexMap<u32, u32, fnv::FnvBuildHasher>>(state.clone(), count, bench);
}

pub fn insert_removals(c: &mut Criterion) {
    let state = fnv::FnvBuildHasher::default();
    let mut group = c.benchmark_group("remove-reinsert");
    bench_remove_reinserts(&state, 10, &mut group);
    bench_remove_reinserts(&state, 100, &mut group);
    bench_remove_reinserts(&state, 500, &mut group);
    bench_remove_reinserts(&state, 1_000, &mut group);
    bench_remove_reinserts(&state, 5_000, &mut group);
    bench_remove_reinserts(&state, 10_000, &mut group);
    bench_remove_reinserts(&state, 50_000, &mut group);
    bench_remove_reinserts(&state, 100_000, &mut group);
    bench_remove_reinserts(&state, 500_000, &mut group);
    bench_remove_reinserts(&state, 1_000_000, &mut group);
}

fn get_entries<M: Map<fnv::FnvBuildHasher>>(
    state: fnv::FnvBuildHasher,
    count: usize,
    bench: &mut BenchmarkGroup<'_, WallTime>,
) {
    bench.bench_function(BenchmarkId::new(M::label(), count), |b| {
        let rng = fastrand::Rng::with_seed(0);
        let mut keys = Vec::with_capacity(count);
        let mut map = M::with_hasher(state.clone());

        for _ in 0..count {
            let key = rng.u32(..);
            let value = rng.u32(..);
            map.insert(key, value);
            keys.push(key);
        }

        rng.shuffle(&mut keys);

        let mut key_index = 0;
        b.iter_batched(
            || {
                key_index += 1;
                if key_index == keys.len() {
                    key_index = 0;
                }
                key_index
            },
            |key_index| {
                map.get(&keys[key_index]).unwrap();
            },
            BatchSize::SmallInput,
        );
    });
}

fn bench_gets(state: &fnv::FnvBuildHasher, count: usize, bench: &mut BenchmarkGroup<'_, WallTime>) {
    get_entries::<BudMap<u32, u32, fnv::FnvBuildHasher>>(state.clone(), count, bench);
    get_entries::<HashMap<u32, u32, fnv::FnvBuildHasher>>(state.clone(), count, bench);
    get_entries::<IndexMap<u32, u32, fnv::FnvBuildHasher>>(state.clone(), count, bench);
}

pub fn gets(c: &mut Criterion) {
    let state = fnv::FnvBuildHasher::default();
    let mut group = c.benchmark_group("gets");
    bench_gets(&state, 10, &mut group);
    bench_gets(&state, 100, &mut group);
    bench_gets(&state, 500, &mut group);
    bench_gets(&state, 1_000, &mut group);
    bench_gets(&state, 5_000, &mut group);
    bench_gets(&state, 10_000, &mut group);
    bench_gets(&state, 50_000, &mut group);
    bench_gets(&state, 100_000, &mut group);
    bench_gets(&state, 500_000, &mut group);
    bench_gets(&state, 1_000_000, &mut group);
}

pub fn benchmarks(c: &mut Criterion) {
    fills(c);
    insert_removals(c);
    gets(c);
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);
