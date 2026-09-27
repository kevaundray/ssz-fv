//! Generalized indices, proof frontiers, and type-level SSZ paths.

use crate::{Arena, Nat};
use crate::types::{ChunkPosition, Desc, Error, PathStep, Reason, Result};

fn scratch<'a>() -> Error<'a> {
    Error::new(Reason::ScratchExhausted)
}

fn word_count<'a>(bits: u128) -> Result<'a, usize> {
    usize::try_from(bits / 64 + u128::from(bits % 64 != 0)).map_err(|_| scratch())
}

fn low_mask(bits: u32) -> u64 {
    if bits == 64 { u64::MAX } else { (1u64 << bits) - 1 }
}

fn range_word(word: usize, start: u128, stop: u128) -> u64 {
    let base = word as u128 * 64;
    let lo = start.saturating_sub(base).min(64) as u32;
    let hi = stop.saturating_sub(base).min(64) as u32;
    low_mask(hi) & !low_mask(lo)
}

fn make_nat<'a, F>(words: usize, arena: &mut Arena<'a>, mut fill: F) -> Result<'a, Nat<'a>>
where
    F: FnMut(usize) -> u64,
{
    match words {
        0 => Ok(Nat::ZERO),
        1 => Ok(Nat::Small(fill(0))),
        _ => Ok(Nat::Large(arena.slice_with(words, |i, _| Ok(fill(i)))?)),
    }
}

fn shifted_word(index: Nat<'_>, shift: u128, word: usize) -> u64 {
    let Some(offset) = usize::try_from(shift / 64).ok().and_then(|n| n.checked_add(word)) else {
        return 0;
    };
    let bits = (shift % 64) as u32;
    let low = index.word(offset) >> bits;
    if bits == 0 {
        low
    } else {
        low | (offset.checked_add(1).map_or(0, |n| index.word(n)) << (64 - bits))
    }
}

fn shift_xor<'a>(index: Nat<'a>, shift: u128, flip: bool, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    let words = word_count(index.bit_len().saturating_sub(shift))?.max(usize::from(flip));
    make_nat(words, arena, |i| shifted_word(index, shift, i) ^ u64::from(flip && i == 0))
}

/// Raw natural logarithm, including `depth(0) == 0`.
pub fn depth(index: Nat<'_>) -> u128 {
    index.bit_len().saturating_sub(1)
}

/// The checked `gindexDepth` operation: zero is not a generalized index.
pub fn checked_depth<'a>(index: Nat<'a>) -> Result<'a, u128> {
    if index.is_zero() { Err(Error::one(Reason::NotAGindex, index)) } else { Ok(depth(index)) }
}

pub fn length<'a>(index: Nat<'a>) -> Result<'a, u128> {
    let result = checked_depth(index)?;
    if result == 0 { Err(Error::new(Reason::RootHasNoBranch)) } else { Ok(result) }
}

pub fn bit(index: Nat<'_>, position: u128) -> bool {
    index.bit(position)
}

pub fn below<'a>(index: Nat<'a>, bits: u128, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    if bits >= index.bit_len() {
        return Ok(index);
    }
    let mut words = word_count(bits)?;
    while words != 0 && index.word(words - 1) & range_word(words - 1, 0, bits) == 0 {
        words -= 1;
    }
    make_nat(words, arena, |i| index.word(i) & range_word(i, 0, bits))
}

pub fn sibling<'a>(index: Nat<'a>, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    shift_xor(index, 0, true, arena)
}

pub fn parent<'a>(index: Nat<'a>, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    index.shr(1, arena)
}

pub fn child<'a>(index: Nat<'a>, right: bool, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    if index.is_zero() {
        return Ok(Nat::Small(u64::from(right)));
    }
    let words = word_count(index.bit_len().checked_add(1).ok_or_else(scratch)?)?;
    make_nat(words, arena, |i| {
        (index.word(i) << 1) | if i == 0 { u64::from(right) } else { index.word(i - 1) >> 63 }
    })
}

pub fn concat<'a>(outer: Nat<'a>, inner: Nat<'a>, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    checked_depth(outer)?;
    let inner_depth = checked_depth(inner)?;
    if inner_depth == 0 {
        return Ok(outer);
    }
    if outer == Nat::ONE {
        return Ok(inner);
    }
    let words = word_count(outer.bit_len().checked_add(inner_depth).ok_or_else(scratch)?)?;
    let offset = usize::try_from(inner_depth / 64).map_err(|_| scratch())?;
    let bits = (inner_depth % 64) as u32;
    make_nat(words, arena, |i| {
        let mut upper = 0;
        if let Some(j) = i.checked_sub(offset) {
            upper = outer.word(j) << bits;
            if bits != 0 && j != 0 {
                upper |= outer.word(j - 1) >> (64 - bits);
            }
        }
        upper | (inner.word(i) & range_word(i, 0, inner_depth))
    })
}

pub fn rebase<'a>(index: Nat<'a>, bits: u128, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    let words = word_count(bits.checked_add(1).ok_or_else(scratch)?)?;
    make_nat(words, arena, |i| {
        (index.word(i) & range_word(i, 0, bits)) | range_word(i, bits, bits + 1)
    })
}

pub fn path_indices<'a>(index: Nat<'a>, arena: &mut Arena<'a>) -> Result<'a, &'a [Nat<'a>]> {
    let count = usize::try_from(length(index)?).map_err(|_| scratch())?;
    arena.slice_with(count, |i, arena| index.shr(i as u128, arena))
}

pub fn branch_indices<'a>(index: Nat<'a>, arena: &mut Arena<'a>) -> Result<'a, &'a [Nat<'a>]> {
    let count = usize::try_from(length(index)?).map_err(|_| scratch())?;
    arena.slice_with(count, |i, arena| shift_xor(index, i as u128, true, arena))
}

// Compare prefixes without allocating the large ancestor numbers. The optional
// low-bit flip is used only on non-root nodes, so their bit length is unchanged.
pub(crate) fn prefix_equal(left: Nat<'_>, left_shift: u128, flip: bool, right: Nat<'_>, right_shift: u128) -> bool {
    let bits = left.bit_len().saturating_sub(left_shift);
    if bits != right.bit_len().saturating_sub(right_shift) {
        return false;
    }
    let words = (bits / 64 + u128::from(bits % 64 != 0)) as usize;
    (0..words).all(|i| {
        (shifted_word(left, left_shift, i) ^ u64::from(flip && i == 0)) == shifted_word(right, right_shift, i)
    })
}

pub fn reject_ancestors<'a>(indices: &[Nat<'a>], claim: Nat<'a>, ancestors: &[Nat<'a>]) -> Result<'a, ()> {
    if ancestors.iter().any(|ancestor| indices.contains(ancestor)) {
        Err(Error::one(Reason::NestedIndex, claim))
    } else {
        Ok(())
    }
}

pub fn reject_claim_paths<'a>(indices: &[Nat<'a>], claims: &[Nat<'a>]) -> Result<'a, ()> {
    for &claim in claims {
        let claim_depth = length(claim)?;
        for &ancestor in indices {
            let ancestor_depth = depth(ancestor);
            if ancestor_depth != 0 && ancestor_depth < claim_depth
                && prefix_equal(claim, claim_depth - ancestor_depth, false, ancestor, 0)
            {
                return Err(Error::one(Reason::NestedIndex, claim));
            }
        }
    }
    Ok(())
}

pub fn reject_related<'a>(indices: &[Nat<'a>]) -> Result<'a, ()> {
    if indices.is_empty() {
        return Err(Error::new(Reason::EmptyRequest));
    }
    for (i, index) in indices.iter().enumerate() {
        if indices[..i].contains(index) {
            return Err(Error::new(Reason::RepeatedIndex));
        }
    }
    reject_claim_paths(indices, indices)
}

pub fn collect_path_indices<'a>(indices: &[Nat<'a>], arena: &mut Arena<'a>) -> Result<'a, &'a [Nat<'a>]> {
    let mut count = 0usize;
    for &index in indices {
        count = count.checked_add(usize::try_from(length(index)?).map_err(|_| scratch())?).ok_or_else(scratch)?;
    }
    let mut claim = 0usize;
    let mut level = 0u128;
    arena.slice_with(count, |_, arena| {
        let index = indices[claim].shr(level, arena)?;
        level += 1;
        if level == depth(indices[claim]) {
            claim += 1;
            level = 0;
        }
        Ok(index)
    })
}

fn is_helper(indices: &[Nat<'_>], claim: usize, level: u128) -> bool {
    let index = indices[claim];
    let node_depth = depth(index) - level;
    for (other, &other_index) in indices.iter().enumerate() {
        let other_depth = depth(other_index);
        if other_depth >= node_depth {
            let shift = other_depth - node_depth;
            if prefix_equal(index, level, true, other_index, shift) {
                return false;
            }
            if other < claim && prefix_equal(index, level, false, other_index, shift) {
                return false;
            }
        }
    }
    true
}

pub fn helper_indices<'a>(indices: &[Nat<'a>], arena: &mut Arena<'a>) -> Result<'a, &'a [Nat<'a>]> {
    reject_related(indices)?;
    // Count the frontier itself, not the (potentially much larger) union of paths.
    let mut count = 0usize;
    for (claim, &index) in indices.iter().enumerate() {
        for level in 0..depth(index) {
            if is_helper(indices, claim, level) {
                count = count.checked_add(1).ok_or_else(scratch)?;
            }
        }
    }
    let mut claim = 0usize;
    let mut level = 0u128;
    let helpers = arena.mutable_slice_with(count, |_, arena| loop {
        let index = indices[claim];
        let candidate_level = level;
        let include = is_helper(indices, claim, level);
        level += 1;
        if level == depth(index) {
            claim += 1;
            level = 0;
        }
        if include {
            return shift_xor(index, candidate_level, true, arena);
        }
    })?;
    helpers.sort_unstable_by(|a, b| b.cmp(a));
    Ok(helpers)
}

/// The default progressive spine starts at index 2 and has widths 1, 4, 16, ... .
pub fn progressive_chunk_index<'a>(chunk: Nat<'a>, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    // Before level k the spine holds (4^k - 1)/3 chunks. Those thresholds
    // consist of alternating one bits, permitting a single output allocation.
    let mut subtree_depth = depth(chunk) / 2 * 2;
    let threshold_bits = subtree_depth + 1;
    let threshold_words = word_count(threshold_bits)?;
    let mut order = chunk.bit_len().cmp(&threshold_bits);
    if order == core::cmp::Ordering::Equal {
        for i in (0..threshold_words).rev() {
            order = chunk.word(i).cmp(&(0x5555_5555_5555_5555 & range_word(i, 0, threshold_bits)));
            if order != core::cmp::Ordering::Equal {
                break;
            }
        }
    }
    if order != core::cmp::Ordering::Less {
        subtree_depth += 2;
    }
    let level = subtree_depth / 2;
    let leading = subtree_depth.checked_add(level).and_then(|n| n.checked_add(2)).ok_or_else(scratch)?;
    let words = word_count(leading.checked_add(1).ok_or_else(scratch)?)?;
    let mut borrow = false;
    make_nat(words, arena, |i| {
        let offset = 0x5555_5555_5555_5555 & range_word(i, 0, subtree_depth);
        let (difference, first) = chunk.word(i).overflowing_sub(offset);
        let (remainder, second) = difference.overflowing_sub(u64::from(borrow));
        borrow = first || second;
        remainder | range_word(i, subtree_depth + 1, subtree_depth + level + 1)
            | range_word(i, leading, leading + 1)
    })
}

pub fn next_pow2<'a>(count: Nat<'a>, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    if count <= Nat::ONE {
        return Ok(Nat::ONE);
    }
    if count.is_power_of_two() {
        return Ok(count);
    }
    Nat::ONE.shl(count.bit_len(), arena)
}

pub fn item_length<'a>(desc: &Desc<'a>) -> Nat<'a> {
    match desc {
        Desc::Bool => Nat::ONE,
        Desc::Uint(width) => *width,
        _ => Nat::Small(32),
    }
}

fn ceil_shift<'a>(value: Nat<'a>, shift: u32, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    if value.word(0) & low_mask(shift) == 0 {
        return value.shr(shift as u128, arena);
    }
    let mut words = word_count(value.bit_len().saturating_sub(shift as u128))?;
    if words == 0 {
        return Ok(Nat::ONE);
    }
    if (0..words).all(|i| shifted_word(value, shift as u128, i) == u64::MAX) {
        words = words.checked_add(1).ok_or_else(scratch)?;
    }
    let mut carry = true;
    make_nat(words, arena, |i| {
        let (word, overflow) = shifted_word(value, shift as u128, i).overflowing_add(u64::from(carry));
        carry = overflow;
        word
    })
}

fn packing_shift(width: Nat<'_>) -> Option<u32> {
    let bytes = width.to_u64()?;
    if bytes <= 32 && bytes.is_power_of_two() { Some(5 - bytes.trailing_zeros()) } else { None }
}

pub fn chunk_count<'a>(desc: &Desc<'a>, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    match desc {
        Desc::Bool | Desc::Uint(_) | Desc::CompatibleUnion(_) => Ok(Nat::ONE),
        Desc::BitVector(length) | Desc::BitList(length) => ceil_shift(*length, 8, arena),
        Desc::ByteVector(length) | Desc::ByteList(length) => ceil_shift(*length, 5, arena),
        Desc::Vector(element, length) | Desc::List(element, length) => {
            let width = item_length(element);
            match packing_shift(width) {
                Some(shift) => ceil_shift(*length, shift, arena),
                None => ceil_shift(length.mul(width, arena)?, 5, arena),
            }
        }
        Desc::Container(fields) => Nat::from_u128(fields.len() as u128, arena),
        _ => Err(Error::new(Reason::NoChunkCount)),
    }
}

pub fn position_count<'a>(desc: &Desc<'a>) -> Result<'a, Option<Nat<'a>>> {
    match desc {
        Desc::ProgressiveList(_, _) | Desc::ProgressiveBitList(_) => Ok(None),
        Desc::Vector(_, count) | Desc::ByteVector(count) | Desc::BitVector(count)
        | Desc::List(_, count) | Desc::ByteList(count) | Desc::BitList(count) => Ok(Some(*count)),
        _ => Err(Error::new(Reason::NotSteppable)),
    }
}

pub fn element_type<'a>(desc: &Desc<'a>, step: PathStep<'a>) -> Result<'a, Desc<'a>> {
    match (desc, step) {
        (Desc::Container(fields) | Desc::ProgressiveContainer { fields, .. }, PathStep::Position(index)) => {
            index.to_usize().and_then(|i| fields.get(i)).map(|field| *field.desc)
                .ok_or_else(|| Error::one(Reason::NoSuchField, index))
        }
        (Desc::BitVector(_) | Desc::BitList(_) | Desc::ProgressiveBitList(_), _) => Ok(Desc::Bool),
        (Desc::ByteVector(_) | Desc::ByteList(_), _) => Ok(Desc::Uint(Nat::ONE)),
        (Desc::Vector(element, _) | Desc::List(element, _) | Desc::ProgressiveList(element, _), _) => Ok(**element),
        _ => Err(Error::new(Reason::NotSteppable)),
    }
}

pub fn active_position<'a>(active: &[bool], ordinal: Nat<'a>, arena: &mut Arena<'a>) -> Result<'a, Option<Nat<'a>>> {
    let Some(mut remaining) = ordinal.to_usize() else { return Ok(None); };
    for (position, &present) in active.iter().enumerate() {
        if present {
            if remaining == 0 {
                return Ok(Some(Nat::from_u128(position as u128, arena)?));
            }
            remaining -= 1;
        }
    }
    Ok(None)
}

pub fn layout_position<'a>(active: &[bool], ordinal: Nat<'a>, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    active_position(active, ordinal, arena)?.ok_or_else(|| Error::one(Reason::NoSuchField, ordinal))
}

pub fn chunk_position<'a>(desc: &Desc<'a>, step: PathStep<'a>, arena: &mut Arena<'a>) -> Result<'a, ChunkPosition<'a>> {
    let width = item_length(&element_type(desc, step)?);
    match (desc, step) {
        (Desc::ProgressiveContainer { active, .. }, PathStep::Position(ordinal)) => {
            Ok(ChunkPosition { chunk: layout_position(active, ordinal, arena)?, start: Nat::ZERO, stop: width })
        }
        (Desc::Container(_), PathStep::Position(ordinal)) => {
            Ok(ChunkPosition { chunk: ordinal, start: Nat::ZERO, stop: width })
        }
        (_, PathStep::Position(position)) => {
            if let Some(count) = position_count(desc)? {
                if position >= count {
                    return Err(Error::one(Reason::NoSuchPosition, position));
                }
            }
            match desc {
                Desc::BitVector(_) | Desc::BitList(_) | Desc::ProgressiveBitList(_) => {
                    Ok(ChunkPosition { chunk: position.shr(8, arena)?, start: Nat::ZERO, stop: Nat::ZERO })
                }
                _ => {
                    if let Some(shift) = packing_shift(width) {
                        let start = (position.word(0) & low_mask(shift)) << (5 - shift);
                        return Ok(ChunkPosition {
                            chunk: position.shr(shift as u128, arena)?,
                            start: Nat::Small(start),
                            stop: Nat::Small(start + (1u64 << (5 - shift))),
                        });
                    }
                    let (chunk, remainder) = position.mul(width, arena)?.div_rem_small(32, arena)?;
                    let start = Nat::Small(remainder);
                    Ok(ChunkPosition { chunk, start, stop: start.add(width, arena)? })
                }
            }
        }
        _ => Err(Error::new(Reason::NotSteppable)),
    }
}

pub fn mixes_in(desc: &Desc<'_>, step: PathStep<'_>) -> bool {
    matches!((desc, step),
        (Desc::List(_, _) | Desc::ByteList(_) | Desc::BitList(_) | Desc::ProgressiveList(_, _)
            | Desc::ProgressiveBitList(_), PathStep::Length)
        | (Desc::ProgressiveContainer { .. }, PathStep::ActiveFields)
        | (Desc::CompatibleUnion(_), PathStep::Selector))
}

pub fn resolve_step<'a>(desc: &Desc<'a>, step: PathStep<'a>, arena: &mut Arena<'a>) -> Result<'a, (Nat<'a>, Option<Desc<'a>>)> {
    if matches!(desc, Desc::Bool | Desc::Uint(_)) {
        return Err(Error::new(Reason::NoParts));
    }
    match step {
        PathStep::Length | PathStep::ActiveFields | PathStep::Selector => {
            if !mixes_in(desc, step) {
                return Err(Error::new(Reason::NoMixin));
            }
            Ok((Nat::Small(3), None))
        }
        PathStep::Position(ordinal) => {
            match desc {
                Desc::CompatibleUnion(variants) => {
                    let option = variants.iter().find(|variant| variant.selector == ordinal)
                        .ok_or_else(|| Error::one(Reason::NoSuchOption, ordinal))?;
                    Ok((Nat::Small(2), Some(*option.desc)))
                }
                Desc::ProgressiveContainer { .. } | Desc::ProgressiveList(_, _) | Desc::ProgressiveBitList(_) => {
                    let placed = chunk_position(desc, step, arena)?;
                    Ok((progressive_chunk_index(placed.chunk, arena)?, Some(element_type(desc, step)?)))
                }
                _ => {
                    let placed = chunk_position(desc, step, arena)?;
                    let count = chunk_count(desc, arena)?;
                    let leaf_depth = if count <= Nat::ONE {
                        0
                    } else {
                        count.bit_len() - u128::from(count.is_power_of_two())
                    };
                    let mixed = matches!(desc, Desc::List(_, _) | Desc::ByteList(_) | Desc::BitList(_));
                    let index = rebase(placed.chunk, leaf_depth + u128::from(mixed), arena)?;
                    Ok((index, Some(element_type(desc, step)?)))
                }
            }
        }
    }
}

pub fn generalized_index<'a>(desc: &Desc<'a>, path: &[PathStep<'a>], arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    let Some((&step, rest)) = path.split_first() else { return Ok(Nat::ONE); };
    let (index, target) = resolve_step(desc, step, arena)?;
    match target {
        None if rest.is_empty() => Ok(index),
        None => Err(Error::new(Reason::NoPartsMixin)),
        Some(child) => {
            let inner = generalized_index(&child, rest, arena)?;
            concat(index, inner, arena)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Field, Variant};
    use core::mem::MaybeUninit;

    #[test]
    fn arbitrary_depth_splices_rebase_without_truncation() {
        let mut storage = [MaybeUninit::uninit(); 16_384];
        let mut arena = Arena::new(&mut storage);
        let outer = Nat::Large(&[5, 0, 2]);
        let inner = Nat::Large(&[u64::MAX, 1]);
        let joined = concat(outer, inner, &mut arena).unwrap();
        assert_eq!(joined, Nat::Large(&[u64::MAX, 5, 0, 2]));
        assert_eq!(length(joined).unwrap(), 193);
        assert_eq!(rebase(joined, 64, &mut arena).unwrap(), inner);
        assert_eq!(below(joined, 128, &mut arena).unwrap(), Nat::Large(&[u64::MAX, 5]));
        assert_eq!(parent(child(joined, true, &mut arena).unwrap(), &mut arena).unwrap(), joined);
        assert_eq!(sibling(Nat::ZERO, &mut arena).unwrap(), Nat::ONE);
        assert_eq!(concat(Nat::ZERO, Nat::ZERO, &mut arena).unwrap_err(), Error::one(Reason::NotAGindex, Nat::ZERO));
        let path = path_indices(joined, &mut arena).unwrap();
        assert_eq!(path.len(), 193);
        assert_eq!(path[0], joined);
        assert_eq!(path[192], Nat::Small(2));
        assert_eq!(rebase(Nat::ZERO, u128::MAX, &mut arena).unwrap_err().reason, Reason::ScratchExhausted);
    }

    #[test]
    fn helper_frontier_is_descending_unique_and_excludes_claim_paths() {
        let mut storage = [MaybeUninit::uninit(); 16_384];
        let mut arena = Arena::new(&mut storage);
        let claims = [Nat::Small(8), Nat::Small(9), Nat::Small(14)];
        assert_eq!(helper_indices(&claims, &mut arena).unwrap(), &[Nat::Small(15), Nat::Small(6), Nat::Small(5)]);
        let complete = [2, 3].map(Nat::Small);
        assert!(helper_indices(&complete, &mut arena).unwrap().is_empty());
        let big = Nat::Large(&[7, 2, 4]);
        let helpers = helper_indices(&[big], &mut arena).unwrap();
        let branch = branch_indices(big, &mut arena).unwrap();
        assert_eq!(helpers, branch);
        assert_eq!(helpers[0], Nat::Large(&[6, 2, 4]));
        assert_eq!(helpers[129], Nat::Small(3));
    }

    #[test]
    fn claim_validation_preserves_duplicate_and_request_order_precedence() {
        let cases: &[(&[u64], Reason, u64)] = &[
            (&[], Reason::EmptyRequest, 0),
            (&[0, 1, 0], Reason::RepeatedIndex, 0),
            (&[1, 1], Reason::RepeatedIndex, 0),
            (&[4, 2, 0], Reason::NestedIndex, 4),
            (&[0, 4, 2], Reason::NotAGindex, 0),
            (&[2, 1], Reason::RootHasNoBranch, 0),
            (&[4, 1, 2], Reason::NestedIndex, 4),
            (&[1, 4, 2], Reason::RootHasNoBranch, 0),
            (&[2, 4], Reason::NestedIndex, 4),
        ];
        for &(values, reason, payload) in cases {
            let mut storage = [MaybeUninit::uninit(); 1024];
            let mut arena = Arena::new(&mut storage);
            let claims = arena.slice_with(values.len(), |i, _| Ok(Nat::Small(values[i]))).unwrap();
            let error = helper_indices(claims, &mut arena).unwrap_err();
            assert_eq!(error.reason, reason);
            assert_eq!(error.args[0], Nat::Small(payload));
        }
    }

    #[test]
    fn progressive_positions_follow_every_small_spine_boundary_and_large_levels() {
        for chunk in 0..4096u64 {
            let mut storage = [MaybeUninit::uninit(); 256];
            let mut arena = Arena::new(&mut storage);
            let mut remaining = chunk;
            let mut width = 1;
            let mut spine = 2;
            while remaining >= width {
                remaining -= width;
                width *= 4;
                spine = spine * 2 + 1;
            }
            assert_eq!(progressive_chunk_index(Nat::Small(chunk), &mut arena).unwrap(),
                Nat::Small(spine * 2 * width + remaining));
        }
        let mut storage = [MaybeUninit::uninit(); 256];
        let mut arena = Arena::new(&mut storage);
        let boundary = Nat::Large(&[0x5555_5555_5555_5555, 0x5555_5555_5555_5555]);
        assert_eq!(progressive_chunk_index(boundary, &mut arena).unwrap(), Nat::Large(&[0, 0, u64::MAX - 1, 5]));
        let before = Nat::Large(&[0x5555_5555_5555_5554, 0x5555_5555_5555_5555]);
        assert_eq!(progressive_chunk_index(before, &mut arena).unwrap(),
            Nat::Large(&[u64::MAX, 0xbfff_ffff_ffff_ffff, 0xbfff_ffff_ffff_ffff]));
    }

    #[test]
    fn packed_offsets_and_declared_capacities_remain_arbitrary_precision() {
        let mut storage = [MaybeUninit::uninit(); 2048];
        let mut arena = Arena::new(&mut storage);
        let uint = Desc::Uint(Nat::Small(2));
        let capacity = Nat::Large(&[0, 0, 1]);
        let desc = Desc::List(&uint, capacity);
        let index = Nat::Large(&[31, 1]);
        let position = chunk_position(&desc, PathStep::Position(index), &mut arena).unwrap();
        assert_eq!(position, ChunkPosition { chunk: Nat::Small((1u64 << 60) + 1), start: Nat::Small(30), stop: Nat::Small(32) });
        assert_eq!(chunk_count(&desc, &mut arena).unwrap(), Nat::Large(&[0, 1u64 << 60]));
        assert_eq!(generalized_index(&desc, &[PathStep::Position(index)], &mut arena).unwrap(),
            Nat::Large(&[(1u64 << 60) + 1, 1u64 << 61]));
        assert_eq!(chunk_position(&desc, PathStep::Position(capacity), &mut arena).unwrap_err(),
            Error::one(Reason::NoSuchPosition, capacity));
        let rounded = Desc::ByteList(Nat::Large(&[u64::MAX, 31]));
        assert_eq!(chunk_count(&rounded, &mut arena).unwrap(), Nat::Large(&[0, 1]));
        let bits = Desc::ProgressiveBitList(Some(Nat::ONE));
        assert_eq!(chunk_position(&bits, PathStep::Position(Nat::Small(256)), &mut arena).unwrap(),
            ChunkPosition { chunk: Nat::ONE, start: Nat::ZERO, stop: Nat::ZERO });
        assert_eq!(generalized_index(&bits, &[PathStep::Position(Nat::Small(256))], &mut arena).unwrap(), Nat::Small(40));
    }

    #[test]
    fn progressive_field_ordinals_and_terminal_mixins_preserve_path_errors() {
        let mut storage = [MaybeUninit::uninit(); 2048];
        let mut arena = Arena::new(&mut storage);
        let boolean = Desc::Bool;
        let fields = [Field { name: "a", desc: &boolean }, Field { name: "b", desc: &boolean }];
        let desc = Desc::ProgressiveContainer { active: &[true, false, false, true], fields: &fields };
        let field = PathStep::Position(Nat::ONE);
        assert_eq!(chunk_position(&desc, field, &mut arena).unwrap(),
            ChunkPosition { chunk: Nat::Small(3), start: Nat::ZERO, stop: Nat::ONE });
        assert_eq!(generalized_index(&desc, &[field], &mut arena).unwrap(), Nat::Small(42));
        assert_eq!(generalized_index(&desc, &[PathStep::ActiveFields], &mut arena).unwrap(), Nat::Small(3));
        assert_eq!(generalized_index(&desc, &[PathStep::ActiveFields, field], &mut arena).unwrap_err().reason, Reason::NoPartsMixin);
        assert_eq!(generalized_index(&desc, &[PathStep::Length], &mut arena).unwrap_err().reason, Reason::NoMixin);
        assert_eq!(generalized_index(&boolean, &[PathStep::Length], &mut arena).unwrap_err().reason, Reason::NoParts);
        assert_eq!(generalized_index(&desc, &[field, field], &mut arena).unwrap_err().reason, Reason::NoParts);
        let selector = Nat::Large(&[0, 1]);
        let variants = [Variant { selector, desc: &desc }];
        let union = Desc::CompatibleUnion(&variants);
        assert_eq!(generalized_index(&union, &[PathStep::Position(selector), field], &mut arena).unwrap(), Nat::Small(74));
        assert_eq!(generalized_index(&union, &[field], &mut arena).unwrap_err(), Error::one(Reason::NoSuchOption, Nat::ONE));
        assert_eq!(generalized_index(&union, &[PathStep::Selector], &mut arena).unwrap(), Nat::Small(3));
    }
}
