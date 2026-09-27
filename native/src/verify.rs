//! Raw Merkle reconstruction and width-checked proof verification.
//!
//! Calculators hash the supplied byte strings without imposing chunk widths.
//! Verifiers check every operand before checking the proof's structure.

use crate::hash::{combine, Hash};
use crate::indices;
use crate::{Arena, Error, Nat, Reason, Result};

fn count_error<'a>(
    reason: Reason,
    expected: u128,
    actual: u128,
    arena: &mut Arena<'a>,
) -> Result<'a, Error<'a>> {
    Ok(Error::two(
        reason,
        Nat::from_u128(expected, arena)?,
        Nat::from_u128(actual, arena)?,
    ))
}

fn check_chunk<'a>(node: &[u8], arena: &mut Arena<'a>) -> Result<'a, ()> {
    if node.len() != 32 {
        return Err(count_error(Reason::Count, 32, node.len() as u128, arena)?);
    }
    Ok(())
}

fn check_chunks<'a>(nodes: &[&[u8]], arena: &mut Arena<'a>) -> Result<'a, ()> {
    for node in nodes {
        check_chunk(node, arena)?;
    }
    Ok(())
}

/// Rebuild a branch, accepting arbitrary byte widths for its raw hash operands.
pub fn calculate_merkle_root<'a>(
    leaf: &[u8],
    proof: &[&[u8]],
    index: Nat<'a>,
    arena: &mut Arena<'a>,
) -> Result<'a, Hash> {
    let depth = indices::length(index)?;
    if proof.len() as u128 != depth {
        return Err(count_error(Reason::BranchLength, depth, proof.len() as u128, arena)?);
    }
    // A checked branch index has positive depth, so the first hash always exists.
    let mut node = if index.bit(0) {
        combine(proof[0], leaf)
    } else {
        combine(leaf, proof[0])
    };
    for (level, sibling) in proof.iter().enumerate().skip(1) {
        node = if index.bit(level as u128) {
            combine(sibling, &node)
        } else {
            combine(&node, sibling)
        };
    }
    Ok(node)
}

/// Check leaf, root, and branch widths in that order, then compare the rebuilt root.
pub fn verify_merkle_proof<'a>(
    leaf: &[u8],
    proof: &[&[u8]],
    index: Nat<'a>,
    root: &[u8],
    arena: &mut Arena<'a>,
) -> Result<'a, bool> {
    check_chunk(leaf, arena)?;
    check_chunk(root, arena)?;
    check_chunks(proof, arena)?;
    Ok(calculate_merkle_root(leaf, proof, index, arena)?.as_slice() == root)
}

// Source positions keep input borrows independent of the arena lifetime. Only
// calculated hashes, not copies of the raw input bytes, live in scratch storage.
#[derive(Clone, Copy)]
enum NodeValue {
    Leaf(usize),
    Proof(usize),
    Hashed(Hash),
}

impl NodeValue {
    fn bytes<'b>(&'b self, leaves: &'b [&[u8]], proof: &'b [&[u8]]) -> &'b [u8] {
        match self {
            Self::Leaf(position) => leaves[*position],
            Self::Proof(position) => proof[*position],
            Self::Hashed(hash) => hash,
        }
    }
}

#[derive(Clone, Copy)]
struct Node<'a> {
    // The current generalized index is index >> shift. Keeping a view avoids
    // allocating a new arbitrary-precision integer for every parent.
    index: Nat<'a>,
    shift: u128,
    depth: u128,
    value: NodeValue,
}

impl Node<'_> {
    fn is_right(&self) -> bool {
        self.index.bit(self.shift)
    }

    fn is_sibling_of(&self, other: &Self) -> bool {
        indices::prefix_equal(self.index, self.shift, true, other.index, other.shift)
    }
}

/// Rebuild a multiproof using the descending helper frontier and raw byte operands.
pub fn calculate_multi_merkle_root<'a>(
    leaves: &[&[u8]],
    proof: &[&[u8]],
    indices: &[Nat<'a>],
    arena: &mut Arena<'a>,
) -> Result<'a, Hash> {
    if leaves.len() != indices.len() {
        return Err(count_error(
            Reason::LeafCount, indices.len() as u128, leaves.len() as u128, arena,
        )?);
    }
    let helpers = indices::helper_indices(indices, arena)?;
    if proof.len() != helpers.len() {
        return Err(count_error(
            Reason::ProofLength, helpers.len() as u128, proof.len() as u128, arena,
        )?);
    }
    let count = indices.len().checked_add(helpers.len())
        .ok_or_else(|| Error::new(Reason::ScratchExhausted))?;
    let mut deepest = 0;
    let nodes = arena.mutable_slice_with(count, |position, _| {
        let (index, value) = if position < indices.len() {
            (indices[position], NodeValue::Leaf(position))
        } else {
            let helper = position - indices.len();
            (helpers[helper], NodeValue::Proof(helper))
        };
        let depth = indices::depth(index);
        deepest = deepest.max(depth);
        Ok(Node { index, shift: 0, depth, value })
    })?;

    let mut active = count;
    while deepest != 0 {
        // Leave all indices intact until every sibling check has finished.
        // Only even nodes are changed, and they hash only untouched odd nodes.
        for position in 0..active {
            if nodes[position].depth != deepest {
                continue;
            }
            let sibling = nodes[..active].iter()
                .position(|candidate| nodes[position].is_sibling_of(candidate))
                .ok_or_else(|| Error::new(Reason::ProofIncomplete))?;
            if !nodes[position].is_right() {
                let parent = combine(
                    nodes[position].value.bytes(leaves, proof),
                    nodes[sibling].value.bytes(leaves, proof),
                );
                nodes[position].value = NodeValue::Hashed(parent);
            }
        }

        // Claims and helpers form an antichain with unique indices. Thus their
        // parents remain unique, and interleaving kept nodes with parents is
        // equivalent to foldLevel's parents ++ kept for lookup and hashing.
        // Compact in place: no node arrays or large indices are allocated here.
        let mut written = 0;
        for position in 0..active {
            if nodes[position].depth == deepest {
                if nodes[position].is_right() {
                    continue;
                }
                nodes[position].shift += 1;
                nodes[position].depth -= 1;
            }
            if written != position {
                nodes[written] = nodes[position];
            }
            written += 1;
        }
        active = written;
        deepest -= 1;
    }

    for node in &nodes[..active] {
        if indices::prefix_equal(node.index, node.shift, false, Nat::ONE, 0) {
            // Root claims were refused by helper_indices, so any root here
            // was produced by at least one hash, even for raw-width operands.
            if let NodeValue::Hashed(root) = node.value {
                return Ok(root);
            }
        }
    }
    Err(Error::new(Reason::ProofIncomplete))
}

/// Check root, leaf, and proof widths in that order before structural validation.
pub fn verify_merkle_multiproof<'a>(
    leaves: &[&[u8]],
    proof: &[&[u8]],
    indices: &[Nat<'a>],
    root: &[u8],
    arena: &mut Arena<'a>,
) -> Result<'a, bool> {
    check_chunk(root, arena)?;
    check_chunks(leaves, arena)?;
    check_chunks(proof, arena)?;
    Ok(calculate_multi_merkle_root(leaves, proof, indices, arena)?.as_slice() == root)
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::MaybeUninit;

    #[test]
    fn raw_width_boundaries_are_not_checked_verification_boundaries() {
        let bytes = [7; 64];
        let root = combine(&bytes[..32], &bytes[32..]);
        let mut storage = [MaybeUninit::uninit(); 4096];
        let mut arena = Arena::new(&mut storage);
        assert_eq!(calculate_merkle_root(
            &bytes[..31], &[&bytes[31..]], Nat::Small(2), &mut arena,
        ).unwrap(), root);
        assert_eq!(calculate_multi_merkle_root(
            &[&bytes[..31]], &[&bytes[31..]], &[Nat::Small(2)], &mut arena,
        ).unwrap(), root);
        let count = Error::two(Reason::Count, Nat::Small(32), Nat::Small(31));
        assert_eq!(verify_merkle_proof(
            &bytes[..31], &[&bytes[31..]], Nat::Small(2), &root, &mut arena,
        ), Err(count));
        assert_eq!(verify_merkle_multiproof(
            &[&bytes[..31]], &[&bytes[31..]], &[Nat::Small(2)], &root, &mut arena,
        ), Err(count));
    }

    #[test]
    fn single_width_and_structure_errors_have_upstream_precedence() {
        let bytes = [0; 32];
        let mut storage = [MaybeUninit::uninit(); 256];
        let mut arena = Arena::new(&mut storage);
        for (leaf, root, proof, actual) in [
            (&bytes[..31], &bytes[..30], &bytes[..29], 31),
            (&bytes[..], &bytes[..30], &bytes[..29], 30),
            (&bytes[..], &bytes[..], &bytes[..29], 29),
        ] {
            assert_eq!(verify_merkle_proof(leaf, &[proof], Nat::ZERO, root, &mut arena),
                Err(Error::two(Reason::Count, Nat::Small(32), Nat::Small(actual))));
        }
        assert_eq!(verify_merkle_proof(&bytes, &[&bytes], Nat::ZERO, &bytes, &mut arena),
            Err(Error::one(Reason::NotAGindex, Nat::ZERO)));
        assert_eq!(calculate_merkle_root(&bytes, &[&bytes], Nat::ONE, &mut arena),
            Err(Error::new(Reason::RootHasNoBranch)));
        assert_eq!(calculate_merkle_root(&bytes, &[&bytes], Nat::Small(4), &mut arena),
            Err(Error::two(Reason::BranchLength, Nat::Small(2), Nat::ONE)));
    }

    #[test]
    fn multiproof_width_checks_precede_counts_and_claim_validation() {
        let bytes = [0; 32];
        let mut storage = [MaybeUninit::uninit(); 4096];
        let mut arena = Arena::new(&mut storage);
        for (root, leaf, proof, actual) in [
            (&bytes[..31], &bytes[..30], &bytes[..29], 31),
            (&bytes[..], &bytes[..30], &bytes[..29], 30),
            (&bytes[..], &bytes[..], &bytes[..29], 29),
        ] {
            assert_eq!(verify_merkle_multiproof(&[leaf], &[proof], &[], root, &mut arena),
                Err(Error::two(Reason::Count, Nat::Small(32), Nat::Small(actual))));
        }
        assert_eq!(calculate_multi_merkle_root(&[&bytes], &[], &[], &mut arena),
            Err(Error::two(Reason::LeafCount, Nat::ZERO, Nat::ONE)));
        assert_eq!(calculate_multi_merkle_root(&[], &[&bytes], &[], &mut arena),
            Err(Error::new(Reason::EmptyRequest)));
        assert_eq!(calculate_multi_merkle_root(
            &[&bytes, &bytes], &[], &[Nat::ZERO, Nat::ZERO], &mut arena,
        ), Err(Error::new(Reason::RepeatedIndex)));
        assert_eq!(calculate_multi_merkle_root(
            &[&bytes, &bytes], &[], &[Nat::Small(4), Nat::Small(2)], &mut arena,
        ), Err(Error::one(Reason::NestedIndex, Nat::Small(4))));
        assert_eq!(calculate_multi_merkle_root(&[&bytes], &[], &[Nat::ZERO], &mut arena),
            Err(Error::one(Reason::NotAGindex, Nat::ZERO)));
        assert_eq!(calculate_multi_merkle_root(&[&bytes], &[], &[Nat::ONE], &mut arena),
            Err(Error::new(Reason::RootHasNoBranch)));
        assert_eq!(calculate_multi_merkle_root(&[&bytes], &[], &[Nat::Small(2)], &mut arena),
            Err(Error::two(Reason::ProofLength, Nat::ONE, Nat::ZERO)));
    }

    #[test]
    fn raw_multiproof_uses_descending_helpers_and_unsorted_mixed_depth_claims() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        let left = combine(&combine(b"eight", b"nine"), &combine(b"ten", b"eleven"));
        let root = combine(&left, b"three");
        assert_eq!(calculate_multi_merkle_root(
            &[b"eleven", b"eight"], &[b"ten", b"nine", b"three"],
            &[Nat::Small(11), Nat::Small(8)], &mut arena,
        ).unwrap(), root);
        assert_eq!(calculate_multi_merkle_root(
            &[b"five", b"three", b"four"], &[],
            &[Nat::Small(5), Nat::Small(3), Nat::Small(4)], &mut arena,
        ).unwrap(), combine(&combine(b"four", b"five"), b"three"));
        assert_eq!(calculate_multi_merkle_root(
            &[b"", b""], &[], &[Nat::Small(2), Nat::Small(3)], &mut arena,
        ).unwrap(), combine(b"", b""));
    }

    #[test]
    fn well_formed_proofs_return_false_for_a_wrong_root() {
        let leaves = [[1; 32], [2; 32], [3; 32], [4; 32]];
        let left = combine(&leaves[0], &leaves[1]);
        let right = combine(&leaves[2], &leaves[3]);
        let root = combine(&left, &right);
        let mut wrong = root;
        wrong[0] ^= 1;
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        for (expected, valid) in [(&root, true), (&wrong, false)] {
            assert_eq!(verify_merkle_proof(
                &leaves[3], &[&leaves[2], &left], Nat::Small(7), expected, &mut arena,
            ), Ok(valid));
            assert_eq!(verify_merkle_multiproof(
                &[&leaves[3], &leaves[0]], &[&leaves[2], &leaves[1]],
                &[Nat::Small(7), Nat::Small(4)], expected, &mut arena,
            ), Ok(valid));
        }
    }

    #[test]
    fn reconstruction_reads_branch_bits_beyond_machine_word_depth() {
        let index = Nat::Large(&[0x8000_0000_0000_0001, 2, 4]);
        let leaf = [1; 32];
        let sibling = [2; 32];
        let proof = [&sibling[..]; 130];
        let mut expected = leaf;
        for level in 0..130 {
            expected = if matches!(level, 0 | 63 | 65) {
                combine(&sibling, &expected)
            } else {
                combine(&expected, &sibling)
            };
        }
        let mut storage = [MaybeUninit::uninit(); 65536];
        let mut arena = Arena::new(&mut storage);
        assert_eq!(calculate_merkle_root(&leaf, &proof, index, &mut arena).unwrap(), expected);
        assert_eq!(calculate_multi_merkle_root(&[&leaf], &proof, &[index], &mut arena).unwrap(), expected);
    }
}
