//! Sparse SSZ tree roots with capacity-independent working storage.

use crate::hash::{combine, Hash};
use crate::{Error, Nat, Reason, Result};

const ZERO: Hash = [0; 32];
const TREE_LEVELS: usize = usize::BITS as usize;
// A completed progressive level consumes 4^level leaves. A usize count can
// therefore complete at most this many levels, regardless of logical depth.
const SPINE_LEVELS: usize = (TREE_LEVELS + 1) / 2;

pub fn zero_subtree(depth: u128) -> Hash {
    let mut node = ZERO;
    for _ in 0..depth {
        node = combine(&node, &node);
    }
    node
}

/// The low 256 bits of a natural number, in little-endian order.
pub fn length_word(count: Nat<'_>) -> Hash {
    let mut word = ZERO;
    for (index, bytes) in word.chunks_exact_mut(8).enumerate() {
        bytes.copy_from_slice(&count.word(index).to_le_bytes());
    }
    word
}

/// The first 256 logical active-field bits, least-significant bit first.
pub fn active_fields_word(active: &[bool]) -> Hash {
    let mut word = ZERO;
    for (index, &bit) in active.iter().take(256).enumerate() {
        word[index / 8] |= (bit as u8) << (index % 8);
    }
    word
}

pub fn mix_in(root: &[u8], word: &[u8]) -> Hash { combine(root, word) }

fn depth_for_count(count: usize) -> u128 {
    if count <= 1 { 0 } else { (usize::BITS - (count - 1).leading_zeros()) as u128 }
}

fn bounded_depth<'a>(count: usize, limit: Option<Nat<'a>>) -> Result<'a, u128> {
    match limit {
        Some(capacity) => {
            if capacity.cmp_usize(count).is_lt() {
                return Err(Error::two(Reason::MerkleizeLimit, Nat::Small(count as u64), capacity));
            }
            Ok(capacity.bit_len() - u128::from(capacity.is_power_of_two()))
        }
        None => Ok(depth_for_count(count)),
    }
}

/// Root the chunks at the declared capacity, or their own count if unbounded.
/// An empty sequence with absent or zero capacity roots to the zero leaf.
pub fn bounded<'a>(chunks: &[Hash], limit: Option<Nat<'a>>) -> Result<'a, Hash> {
    // Refuse an undersized capacity before doing any hashing.
    let depth = bounded_depth(chunks.len(), limit)?;
    if chunks.is_empty() {
        return Ok(zero_subtree(depth));
    }
    let mut accumulator = Accumulator::new();
    for chunk in chunks {
        // A slice cannot supply more than usize::MAX elements.
        accumulator.push_node(*chunk);
    }
    Ok(accumulator.root_at_depth(depth))
}

/// Streaming bounded merkleization, retaining one root per occupied height.
///
/// This stack bounds only the number of concrete leaves addressable by the
/// caller. Declared capacity and the final zero-padding depth are unrestricted.
pub struct Accumulator {
    nodes: [Hash; TREE_LEVELS],
    count: usize,
}

impl Accumulator {
    pub const fn new() -> Self { Self { nodes: [ZERO; TREE_LEVELS], count: 0 } }

    pub fn push<'a>(&mut self, node: Hash) -> Result<'a, ()> {
        if self.count == usize::MAX {
            return Err(Error::new(Reason::OutputTooSmall));
        }
        self.push_node(node);
        Ok(())
    }

    // Requires count < usize::MAX. Bits of count indicate occupied entries.
    fn push_node(&mut self, mut node: Hash) {
        let height = self.count.trailing_ones() as usize;
        for left in &self.nodes[..height] {
            node = combine(left, &node);
        }
        self.nodes[height] = node;
        self.count += 1;
    }

    pub fn finish<'a>(self, limit: Option<Nat<'a>>) -> Result<'a, Hash> {
        let depth = bounded_depth(self.count, limit)?;
        Ok(self.root_at_depth(depth))
    }

    /// Finish at an exact binary-tree depth without materializing 2^depth.
    /// An insufficient depth reports the same capacity failure as `finish`.
    pub fn finish_depth<'a>(self, depth: u128) -> Result<'a, Hash> {
        if depth < depth_for_count(self.count) {
            // An insufficient depth is below usize::BITS, so this capacity
            // fits a small natural on every supported Rust pointer width.
            let capacity = Nat::Small(1u64 << (depth as u32));
            return Err(Error::two(Reason::MerkleizeLimit, Nat::Small(self.count as u64), capacity));
        }
        Ok(self.root_at_depth(depth))
    }

    // Requires depth >= depth_for_count(count).
    fn root_at_depth(&self, depth: u128) -> Hash {
        if self.count == 0 {
            return zero_subtree(depth);
        }
        let mut height = self.count.trailing_zeros() as u128;
        let mut node = self.nodes[height as usize];
        // The rightmost completed subtree is already in node; all other set
        // bits name completed subtrees to its left.
        let remaining = self.count & (self.count - 1);
        let mut zero = ZERO;
        let mut zero_depth = 0;
        while height < depth {
            if height < usize::BITS as u128 && (remaining >> (height as u32)) & 1 != 0 {
                node = combine(&self.nodes[height as usize], &node);
            } else {
                // Advance zero roots only when padding is needed. In
                // particular, a completed tree needs no zero hashing at all.
                while zero_depth < height {
                    zero = combine(&zero, &zero);
                    zero_depth += 1;
                }
                node = combine(&node, &zero);
            }
            height += 1;
        }
        node
    }
}

impl Default for Accumulator {
    fn default() -> Self { Self::new() }
}

/// The progressive 1, 4, 16, ... spine, terminated by a plain zero node.
pub fn progressive(chunks: &[Hash]) -> Hash {
    if chunks.is_empty() {
        return ZERO;
    }
    let mut accumulator = ProgressiveAccumulator::new();
    for chunk in chunks {
        accumulator.push_node(*chunk);
    }
    accumulator.finish()
}

/// Streaming progressive merkleization without a temporary leaf array.
pub struct ProgressiveAccumulator {
    completed: [Hash; SPINE_LEVELS],
    levels: usize,
    current: Accumulator,
    count: usize,
}

impl ProgressiveAccumulator {
    pub const fn new() -> Self {
        Self { completed: [ZERO; SPINE_LEVELS], levels: 0, current: Accumulator::new(), count: 0 }
    }

    pub fn push<'a>(&mut self, node: Hash) -> Result<'a, ()> {
        if self.count == usize::MAX {
            return Err(Error::new(Reason::OutputTooSmall));
        }
        self.push_node(node);
        Ok(())
    }

    // Requires count < usize::MAX, which also bounds the current subtree.
    fn push_node(&mut self, node: Hash) {
        self.current.push_node(node);
        self.count += 1;
        let depth = 2 * self.levels;
        // The last occupied subtree may have a logical width beyond usize;
        // such a subtree can never be filled by an addressable input count.
        if depth < TREE_LEVELS && self.current.count == 1usize << depth {
            self.completed[self.levels] = self.current.nodes[depth];
            self.levels += 1;
            // Count is the occupancy map, so stale entries need not be zeroed.
            self.current.count = 0;
        }
    }

    pub fn finish(self) -> Hash {
        let mut root = ZERO;
        if self.current.count != 0 {
            let here = self.current.root_at_depth((2 * self.levels) as u128);
            root = combine(&here, &root);
        }
        for left in self.completed[..self.levels].iter().rev() {
            root = combine(left, &root);
        }
        root
    }
}

impl Default for ProgressiveAccumulator {
    fn default() -> Self { Self::new() }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn digest(hex: &str) -> Hash {
        let mut out = ZERO;
        for (byte, pair) in out.iter_mut().zip(hex.as_bytes().chunks_exact(2)) {
            fn nibble(byte: u8) -> u8 {
                match byte {
                    b'0'..=b'9' => byte - b'0',
                    b'a'..=b'f' => byte - b'a' + 10,
                    _ => panic!("invalid test vector"),
                }
            }
            *byte = (nibble(pair[0]) << 4) | nibble(pair[1]);
        }
        out
    }

    #[test]
    fn empty_and_singleton_shapes_are_distinct() {
        assert_eq!(bounded(&[], None).unwrap(), ZERO);
        assert_eq!(bounded(&[], Some(Nat::ZERO)).unwrap(), ZERO);
        assert_eq!(bounded(&[], Some(Nat::ONE)).unwrap(), ZERO);
        assert_eq!(bounded(&[], Some(Nat::Small(2))).unwrap(), combine(&ZERO, &ZERO));
        assert_eq!(bounded(&[[1; 32]], None).unwrap(), [1; 32]);
        assert_eq!(progressive(&[]), ZERO);
        assert_eq!(progressive(&[[1; 32]]), combine(&[1; 32], &ZERO));
        assert_eq!(Accumulator::new().finish(None).unwrap(), ZERO);
        assert_eq!(ProgressiveAccumulator::new().finish(), ZERO);
    }

    #[test]
    fn insufficient_capacity_preserves_error_payloads() {
        let chunks = [[1; 32], [2; 32], [3; 32]];
        let expected = Error::two(Reason::MerkleizeLimit, Nat::Small(3), Nat::Small(2));
        assert_eq!(bounded(&chunks, Some(Nat::Small(2))), Err(expected));
        let mut accumulator = Accumulator::new();
        for chunk in chunks { accumulator.push(chunk).unwrap(); }
        assert_eq!(accumulator.finish_depth(1), Err(expected));
        assert_eq!(bounded(&chunks[..1], Some(Nat::ZERO)),
            Err(Error::two(Reason::MerkleizeLimit, Nat::ONE, Nat::ZERO)));
    }

    #[test]
    fn sparse_capacities_and_zero_roots_exceed_word_depth() {
        // Independent vectors from Python hashlib over the upstream recursive
        // subtree definition; no materialized 2^129-leaf tree is necessary.
        assert_eq!(zero_subtree(65), digest(
            "303ce38809ba7a77b660ad0b074af9c6bcd5c02bbff2f3b0248633b0b876e449"));
        let zero129 = digest("6fb8963ceb8052837b3fab4f986921791b82afe3dffe09a5e0fe54f86281a2b4");
        assert_eq!(zero_subtree(129), zero129);
        assert_eq!(bounded(&[], Some(Nat::Large(&[0, 0, 2]))).unwrap(), zero129);
        let chunks = [[1; 32], [2; 32], [3; 32]];
        assert_eq!(bounded(&chunks, Some(Nat::Small(5))).unwrap(), digest(
            "16e7bc9c1de9b5c63df0e8ef884b1006155d390b6e1aee4ffd3844e548ec2d41"));
        let root129 = digest("4b7c68ba7cd417da50a656e3aa29e1b25a1a63360958e2f7f21c1ddac7d7e151");
        assert_eq!(bounded(&chunks, Some(Nat::Large(&[0, 0, 2]))).unwrap(), root129);
        assert_eq!(bounded(&chunks, Some(Nat::Large(&[0, 0, 2, 0]))).unwrap(), root129);
        assert_eq!(bounded(&chunks, Some(Nat::Large(&[1, 0, 2]))).unwrap(), digest(
            "b654443e7e0d715513ea8f04e92378c08a8615c53ec6bafb129f42359f1b7c1d"));
        let mut accumulator = Accumulator::new();
        for chunk in chunks { accumulator.push(chunk).unwrap(); }
        assert_eq!(accumulator.finish_depth(129).unwrap(), root129);
    }

    fn dense_root(chunks: &[Hash], width: usize) -> Hash {
        let mut layer = [ZERO; 128];
        layer[..chunks.len()].copy_from_slice(chunks);
        let mut width = width;
        while width > 1 {
            for index in 0..width / 2 {
                layer[index] = combine(&layer[2 * index], &layer[2 * index + 1]);
            }
            width /= 2;
        }
        layer[0]
    }

    #[test]
    fn streaming_padding_matches_dense_trees_at_carry_boundaries() {
        let mut chunks = [[0; 32]; 65];
        for (index, chunk) in chunks.iter_mut().enumerate() {
            *chunk = [index as u8 + 1; 32];
        }
        for count in 0..=chunks.len() {
            let chunks = &chunks[..count];
            let mut natural = Accumulator::new();
            let mut capacity = Accumulator::new();
            for chunk in chunks {
                natural.push(*chunk).unwrap();
                capacity.push(*chunk).unwrap();
            }
            assert_eq!(natural.finish(None).unwrap(), dense_root(chunks, count.next_power_of_two()),
                "unbounded count={count}");
            assert_eq!(capacity.finish(Some(Nat::Small(128))).unwrap(), dense_root(chunks, 128),
                "bounded count={count}");
        }
    }

    #[test]
    fn progressive_full_levels_and_new_levels_match_reference_vectors() {
        let mut chunks = [[0; 32]; 86];
        for (index, chunk) in chunks.iter_mut().enumerate() {
            *chunk = [index as u8 + 1; 32];
        }
        // Hashlib vectors for the 1,4,16,64 spine, including each transition
        // from a full level to a partially padded, newly opened level.
        for (count, expected) in [
            (1, "037d6dfb3a369a41e01100fdd53c35ee3fb69ddec5830d61e1138d066a4c2285"),
            (2, "2dfe47da19ad9ff11afe44dd8de4db8517cefd5a9bddffe6652b26a1b91ea5ac"),
            (5, "3fd53b812118ddea60b9deab5c72d32b0c4dcfd2c94deda753e6e1d548fbc274"),
            (6, "2e2a2abd4d0e28498ec0cdd817c715b246aa15e7b34767061b7632337188429e"),
            (21, "f148f679afbfebfe5616080a45461aee3d1f4ce2cc752ce824c3f067d2707623"),
            (22, "040be60071c540aafc1d44f366239ab6a41bf8740a38f9d52ab0bbd9cd974c45"),
            (85, "24ea21562226364be74fd2696d0824a4347cfac7dd4b2ae28cd0e9cc22bc341d"),
            (86, "b73c4c427974f47c74c2812d353c966f5dadae70c44f6fe9a15e179b86914977"),
        ] {
            let expected = digest(expected);
            let mut accumulator = ProgressiveAccumulator::new();
            for chunk in &chunks[..count] { accumulator.push(*chunk).unwrap(); }
            assert_eq!(accumulator.finish(), expected, "streaming count={count}");
            assert_eq!(progressive(&chunks[..count]), expected, "slice count={count}");
        }
    }

    #[test]
    fn mixing_words_truncate_only_above_256_logical_bits() {
        let count = Nat::Large(&[
            0x0807060504030201, 0x100f0e0d0c0b0a09,
            0x1817161514131211, 0x201f1e1d1c1b1a19, u64::MAX,
        ]);
        let mut expected = ZERO;
        for (index, byte) in expected.iter_mut().enumerate() { *byte = index as u8 + 1; }
        assert_eq!(length_word(count), expected);
        let mut active = [false; 300];
        for index in [0, 7, 8, 255, 256, 299] { active[index] = true; }
        let mut expected = ZERO;
        expected[0] = 0x81;
        expected[1] = 0x01;
        expected[31] = 0x80;
        assert_eq!(active_fields_word(&active), expected);
    }
}
