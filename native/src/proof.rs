//! Schema-aware Merkle node reads and canonical single/multiproof construction.
//! Walks use logical index bits directly; they do not truncate indices to u64 or
//! materialize a padded tree whose declared capacity exceeds its actual data.

use crate::{Arena, Desc, Error, Nat, Reason, Result, Value};
use crate::hash::{combine, Hash};
use crate::indices;
use crate::layout::{self, Layout};
use crate::merkle::{zero_subtree, Accumulator};

fn ceil_depth(capacity: Nat<'_>) -> u128 {
    let bits = capacity.bit_len();
    if bits == 0 { 0 } else if capacity.is_power_of_two() { bits - 1 } else { bits }
}

fn shifted_word(index: Nat<'_>, offset: u128, word: usize) -> u64 {
    let source = offset / 64 + word as u128;
    let low = usize::try_from(source).ok().map(|i| index.word(i)).unwrap_or(0);
    let shift = (offset % 64) as u32;
    if shift == 0 { low } else {
        let high = usize::try_from(source + 1).ok().map(|i| index.word(i)).unwrap_or(0);
        (low >> shift) | (high << (64 - shift))
    }
}

/// Read a bit window only when its numeric value fits a physical slice index.
/// A window too large for usize denotes a node beyond every physical leaf, not
/// an invalid logical generalized index and not an arithmetic truncation.
fn window(index: Nat<'_>, offset: u128, width: u128) -> Option<usize> {
    let effective = index.bit_len().saturating_sub(offset).min(width);
    if effective == 0 { return Some(0); }
    let words = usize::try_from(effective.div_ceil(64)).ok()?;
    for i in 1..words {
        let held = (effective - i as u128 * 64).min(64);
        let mask = if held == 64 { u64::MAX } else { (1u64 << held as u32) - 1 };
        if shifted_word(index, offset, i) & mask != 0 { return None; }
    }
    let mask = if effective >= 64 { u64::MAX } else { (1u64 << effective as u32) - 1 };
    usize::try_from(shifted_word(index, offset, 0) & mask).ok()
}

fn range_root<'a>(layout: Layout<'a>, start: usize, stop: usize, depth: u128,
    arena: &mut Arena<'a>) -> Result<'a, Hash> {
    let mut tree = Accumulator::new();
    for index in start..stop { tree.push(layout.leaf_root(index, arena)?)?; }
    tree.finish_depth(depth)
}

fn bounded_node<'a>(layout: Layout<'a>, index: Nat<'a>, depth: u128,
    base: usize, tree_depth: u128, arena: &mut Arena<'a>) -> Result<'a, Hash> {
    if depth <= tree_depth {
        let span_depth = tree_depth - depth;
        let position = window(index, 0, depth);
        let start = if span_depth >= usize::BITS as u128 {
            match position { Some(0) => Some(base), _ => None }
        } else {
            position.and_then(|p| p.checked_mul(1usize << span_depth as u32))
                .and_then(|delta| base.checked_add(delta))
        };
        let Some(start) = start.filter(|&at| at < layout.count()) else {
            return Ok(zero_subtree(span_depth));
        };
        let stop = if span_depth >= usize::BITS as u128 { layout.count() }
            else { start.saturating_add(1usize << span_depth as u32).min(layout.count()) };
        range_root(layout, start, stop, span_depth, arena)
    } else {
        // Packed leaves refuse all descent, including descent below padding.
        if layout.is_packed() { return Err(Error::new(Reason::PathIntoPacked)); }
        let below = depth - tree_depth;
        let leaf = window(index, below, tree_depth).and_then(|at| base.checked_add(at));
        let Some((desc, value)) = leaf.and_then(|at| layout.nested(at)) else {
            return Err(Error::new(Reason::PathIntoGap));
        };
        // Rebase is implicit: only the low `below` path bits are consumed by the
        // nested walk. This avoids copying a large index on every nested field.
        node_at(&desc, &value, index, below, arena)
    }
}

fn progressive_from<'a>(layout: Layout<'a>, start: usize, capacity: u128,
    arena: &mut Arena<'a>) -> Result<'a, Hash> {
    if start >= layout.count() { return Ok([0; 32]); }
    let remaining = layout.count() - start;
    let take = usize::try_from(capacity).unwrap_or(remaining).min(remaining);
    // Capacities on a progressive spine are powers of four, starting at one.
    let depth = 127 - capacity.leading_zeros() as u128;
    let left = range_root(layout, start, start + take, depth, arena)?;
    // A nonempty next level requires start<count, which bounds capacity by the
    // physical leaf count. A terminal suffix does not multiply capacity at all.
    let right = if start + take == layout.count() { [0; 32] }
        else { progressive_from(layout, start + take, capacity * 4, arena)? };
    Ok(combine(&left, &right))
}

fn progressive_node<'a>(layout: Layout<'a>, index: Nat<'a>, mut depth: u128,
    arena: &mut Arena<'a>) -> Result<'a, Hash> {
    let mut start = 0u128;
    let mut capacity = 1u128;
    while depth != 0 {
        if start >= layout.count() as u128 { return Err(Error::new(Reason::PathPastSpine)); }
        depth -= 1;
        if !index.bit(depth) {
            let tree_depth = 127 - capacity.leading_zeros() as u128;
            return bounded_node(layout, index, depth, start as usize, tree_depth, arena);
        }
        start += capacity;
        capacity *= 4;
    }
    if start >= layout.count() as u128 { Ok([0; 32]) }
    else { progressive_from(layout, start as usize, capacity, arena) }
}

fn node_at<'a>(desc: &Desc<'a>, value: &Value<'a>, index: Nat<'a>, full_depth: u128,
    arena: &mut Arena<'a>) -> Result<'a, Hash> {
    if full_depth == 0 { return layout::hash_tree_root(desc, value, arena); }
    let layout = layout::layout(desc, value, arena)?;
    let depth = if let Some(word) = layout.mixin {
        let remaining = full_depth - 1;
        if index.bit(remaining) {
            if remaining != 0 { return Err(Error::new(Reason::PathIntoMixin)); }
            return Ok(word);
        }
        remaining
    } else { full_depth };
    match layout.limit {
        Some(capacity) => bounded_node(layout, index, depth, 0, ceil_depth(capacity), arena),
        None => progressive_node(layout, index, depth, arena),
    }
}

/// Unlike proof requests, a node read permits index one and returns the root.
pub fn node_root<'a>(desc: &Desc<'a>, value: &Value<'a>, index: Nat<'a>,
    arena: &mut Arena<'a>) -> Result<'a, Hash> {
    if index.is_zero() { return Err(Error::one(Reason::NotAGindex, index)); }
    node_at(desc, value, index, index.bit_len() - 1, arena)
}

pub fn build_proof<'a>(desc: &Desc<'a>, value: &Value<'a>, index: Nat<'a>,
    arena: &mut Arena<'a>) -> Result<'a, &'a [Hash]> {
    let branches = indices::branch_indices(index, arena)?;
    arena.slice_with(branches.len(), |i, arena| node_root(desc, value, branches[i], arena))
}

pub fn build_multiproof<'a>(desc: &Desc<'a>, value: &Value<'a>, indices: &[Nat<'a>],
    arena: &mut Arena<'a>) -> Result<'a, &'a [Hash]> {
    let helpers = crate::indices::helper_indices(indices, arena)?;
    arena.slice_with(helpers.len(), |i, arena| node_root(desc, value, helpers[i], arena))
}
