//! Minimal, zero-dependency FxHash implementation for fast arena hash-consing and kernel caches.
//! Hash values only affect speed: every table compares the stored data on a hash match.

use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

#[derive(Default, Clone)]
pub struct FxHasher { hash: u64 }

impl FxHasher {
    #[inline]
    fn add(&mut self, word: u64) { self.hash = (self.hash.rotate_left(5) ^ word).wrapping_mul(0x517c_c1b7_2722_0a95); }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for c in &mut chunks { self.add(u64::from_ne_bytes(c.try_into().unwrap())); }
        for &b in chunks.remainder() { self.add(b as u64); }
    }
    #[inline]
    fn write_u8(&mut self, i: u8) { self.add(i as u64); }
    #[inline]
    fn write_u32(&mut self, i: u32) { self.add(i as u64); }
    #[inline]
    fn write_u64(&mut self, i: u64) { self.add(i); }
    #[inline]
    fn write_usize(&mut self, i: usize) { self.add(i as u64); }
    #[inline]
    fn finish(&self) -> u64 { self.hash }
}

pub type FxHashMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;
pub type FxHashSet<V> = HashSet<V, BuildHasherDefault<FxHasher>>;
