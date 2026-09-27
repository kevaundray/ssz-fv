//! Streaming counterparts of Ssz.Codec.Layout and Ssz.Codec.Root.
//! Descriptor validation is separate, as in the upstream executable model.

use core::cmp::Ordering;
use crate::{Arena, Bits, Desc, Error, Field, Nat, Reason, Result, Value};
use crate::hash::Hash;
use crate::merkle::{self, Accumulator, ProgressiveAccumulator};

#[derive(Clone, Copy)]
enum Packed<'a> {
    Bytes(&'a [u8]),
    Bits(Bits<'a>),
    Scalar { value: Nat<'a>, width: usize },
    Basic { values: &'a [Value<'a>], width: usize },
}

#[derive(Clone, Copy)]
enum Nested<'a> {
    Sequence { element: &'a Desc<'a>, values: &'a [Value<'a>] },
    Fields { fields: &'a [Field<'a>], values: &'a [Value<'a>] },
    Progressive { active: &'a [bool], fields: &'a [Field<'a>], values: &'a [Value<'a>] },
    Union { desc: &'a Desc<'a>, value: &'a Value<'a> },
}

#[derive(Clone, Copy)]
enum Leaves<'a> {
    Packed(Packed<'a>),
    Nested(Nested<'a>),
}

/// Leaf views retain original caller data instead of materializing encodings or
/// an array of every nested root. Capacity is a mathematical Nat, not a pointer.
#[derive(Clone, Copy)]
pub(crate) struct Layout<'a> {
    leaves: Leaves<'a>,
    pub(crate) limit: Option<Nat<'a>>,
    pub(crate) mixin: Option<Hash>,
}

fn ceil_div<'a>(n: Nat<'a>, divisor: u64, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    let (whole, rest) = n.div_rem_small(divisor, arena)?;
    if rest == 0 { Ok(whole) } else { whole.add(Nat::ONE, arena) }
}

fn count_word(count: u128) -> Hash {
    let mut result = [0; 32];
    result[..16].copy_from_slice(&count.to_le_bytes());
    result
}

fn scalar<'a>(desc: &Desc<'a>, value: &Value<'a>) -> Result<'a, (Nat<'a>, usize)> {
    match (*desc, *value) {
        (Desc::Bool, Value::Bool(bit)) => Ok((Nat::Small(u64::from(bit)), 1)),
        (Desc::Uint(width), Value::Uint(number)) => {
            // Well-formed SSZ integers have at most 32 bytes. Bad native
            // declarations are outside this routine's validated-schema domain.
            let width = width.to_usize().filter(|&n| n <= 32)
                .ok_or(Error::new(Reason::BadRepresentation))?;
            if number.bit_len() > width as u128 * 8 {
                return Err(Error::new(Reason::WrongType));
            }
            Ok((number, width))
        }
        _ => Err(Error::new(Reason::WrongType)),
    }
}

fn basic_width<'a>(desc: &Desc<'a>) -> Result<'a, Option<usize>> {
    match *desc {
        Desc::Bool => Ok(Some(1)),
        Desc::Uint(width) => width.to_usize().filter(|&n| n <= 32)
            .map(Some).ok_or(Error::new(Reason::BadRepresentation)),
        _ => Ok(None),
    }
}

fn sequence<'a>(element: &'a Desc<'a>, values: &'a [Value<'a>],
    positions: Option<Nat<'a>>, mixin: Option<Hash>, arena: &mut Arena<'a>) -> Result<'a, Layout<'a>> {
    if let Some(width) = basic_width(element)? {
        // Upstream serializeEach checks all packed values before tree traversal.
        for value in values { scalar(element, value)?; }
        let limit = match positions {
            Some(count) => Some(ceil_div(count.mul(Nat::Small(width as u64), arena)?, 32, arena)?),
            None => None,
        };
        Ok(Layout { leaves: Leaves::Packed(Packed::Basic { values, width }), limit, mixin })
    } else {
        Ok(Layout { leaves: Leaves::Nested(Nested::Sequence { element, values }), limit: positions, mixin })
    }
}

pub(crate) fn layout<'a>(desc: &Desc<'a>, value: &Value<'a>, arena: &mut Arena<'a>) -> Result<'a, Layout<'a>> {
    match (*desc, *value) {
        (Desc::Bool | Desc::Uint(_), _) => {
            let (value, width) = scalar(desc, value)?;
            Ok(Layout { leaves: Leaves::Packed(Packed::Scalar { value, width }),
                limit: Some(Nat::Small(width.div_ceil(32) as u64)), mixin: None })
        }
        (Desc::ByteVector(length), Value::Bytes(data)) => {
            if length.cmp_usize(data.len()) != Ordering::Equal {
                return Err(Error::two(Reason::Scope, length, Nat::Small(data.len() as u64)));
            }
            Ok(Layout { leaves: Leaves::Packed(Packed::Bytes(data)),
                limit: Some(Nat::Small(data.len().div_ceil(32) as u64)), mixin: None })
        }
        (Desc::ByteList(limit), Value::Bytes(data)) => {
            if limit.cmp_usize(data.len()) == Ordering::Less {
                return Err(Error::two(Reason::Limit, limit, Nat::Small(data.len() as u64)));
            }
            Ok(Layout { leaves: Leaves::Packed(Packed::Bytes(data)),
                limit: Some(ceil_div(limit, 32, arena)?), mixin: Some(count_word(data.len() as u128)) })
        }
        (Desc::BitVector(length), Value::Bits(data)) => {
            if length.cmp_u128(data.len()) != Ordering::Equal {
                return Err(Error::two(Reason::Scope, length, Nat::from_u128(data.len(), arena)?));
            }
            Ok(Layout { leaves: Leaves::Packed(Packed::Bits(data)),
                limit: Some(ceil_div(length, 256, arena)?), mixin: None })
        }
        (Desc::BitList(limit), Value::Bits(data)) => {
            if limit.cmp_u128(data.len()) == Ordering::Less {
                return Err(Error::two(Reason::Limit, limit, Nat::from_u128(data.len(), arena)?));
            }
            Ok(Layout { leaves: Leaves::Packed(Packed::Bits(data)),
                limit: Some(ceil_div(limit, 256, arena)?), mixin: Some(count_word(data.len())) })
        }
        (Desc::ProgressiveBitList(_), Value::Bits(data)) => {
            // Raw upstream rooting intentionally ignores progressive count limits.
            Ok(Layout { leaves: Leaves::Packed(Packed::Bits(data)), limit: None,
                mixin: Some(count_word(data.len())) })
        }
        (Desc::Vector(element, length), Value::Seq(values)) => {
            if length.cmp_usize(values.len()) != Ordering::Equal {
                return Err(Error::two(Reason::Scope, length, Nat::Small(values.len() as u64)));
            }
            sequence(element, values, Some(length), None, arena)
        }
        (Desc::List(element, limit), Value::Seq(values)) => {
            if limit.cmp_usize(values.len()) == Ordering::Less {
                return Err(Error::two(Reason::Limit, limit, Nat::Small(values.len() as u64)));
            }
            sequence(element, values, Some(limit), Some(count_word(values.len() as u128)), arena)
        }
        (Desc::ProgressiveList(element, _), Value::Seq(values)) => {
            sequence(element, values, None, Some(count_word(values.len() as u128)), arena)
        }
        (Desc::Container(fields), Value::Seq(values)) => {
            if fields.len() != values.len() { return Err(Error::new(Reason::WrongType)); }
            Ok(Layout { leaves: Leaves::Nested(Nested::Fields { fields, values }),
                limit: Some(Nat::Small(fields.len() as u64)), mixin: None })
        }
        (Desc::ProgressiveContainer { active, fields }, Value::Seq(values)) => {
            if fields.len() != values.len() { return Err(Error::new(Reason::WrongType)); }
            let count = active.iter().filter(|&&bit| bit).count();
            if count != fields.len() {
                return Err(Error::two(Reason::LayoutFieldCount,
                    Nat::Small(count as u64), Nat::Small(fields.len() as u64)));
            }
            Ok(Layout { leaves: Leaves::Nested(Nested::Progressive { active, fields, values }),
                limit: None, mixin: Some(merkle::active_fields_word(active)) })
        }
        (Desc::CompatibleUnion(options), Value::Union(selector, value)) => {
            let option = options.iter().find(|option| option.selector == selector)
                .ok_or(Error::one(Reason::UnknownSelector, selector))?;
            if selector.cmp_u128(255) == Ordering::Greater {
                return Err(Error::three(Reason::UnionSelectorRange, selector, Nat::ZERO, Nat::Small(255)));
            }
            Ok(Layout { leaves: Leaves::Nested(Nested::Union { desc: option.desc, value }),
                limit: Some(Nat::ONE), mixin: Some(merkle::length_word(selector)) })
        }
        _ => Err(Error::new(Reason::WrongType)),
    }
}

impl<'a> Layout<'a> {
    pub(crate) fn count(self) -> usize {
        match self.leaves {
            Leaves::Packed(Packed::Bytes(data)) => data.len().div_ceil(32),
            Leaves::Packed(Packed::Bits(bits)) => bits.bytes().len().div_ceil(32),
            Leaves::Packed(Packed::Scalar { width, .. }) => width.div_ceil(32),
            Leaves::Packed(Packed::Basic { values, width }) =>
                ((values.len() as u128 * width as u128).div_ceil(32)) as usize,
            Leaves::Nested(Nested::Sequence { values, .. } | Nested::Fields { values, .. }) => values.len(),
            Leaves::Nested(Nested::Progressive { active, .. }) => active.len(),
            Leaves::Nested(Nested::Union { .. }) => 1,
        }
    }

    pub(crate) fn is_packed(self) -> bool { matches!(self.leaves, Leaves::Packed(_)) }

    pub(crate) fn nested(self, index: usize) -> Option<(Desc<'a>, Value<'a>)> {
        match self.leaves {
            Leaves::Nested(Nested::Sequence { element, values }) => values.get(index).map(|v| (*element, *v)),
            Leaves::Nested(Nested::Fields { fields, values }) =>
                fields.get(index).zip(values.get(index)).map(|(f, v)| (*f.desc, *v)),
            Leaves::Nested(Nested::Progressive { active, fields, values }) => {
                if !active.get(index).copied().unwrap_or(false) { return None; }
                let ordinal = active[..index].iter().filter(|&&bit| bit).count();
                fields.get(ordinal).zip(values.get(ordinal)).map(|(f, v)| (*f.desc, *v))
            }
            Leaves::Nested(Nested::Union { desc, value }) if index == 0 => Some((*desc, *value)),
            _ => None,
        }
    }

    pub(crate) fn leaf_root(self, index: usize, arena: &mut Arena<'a>) -> Result<'a, Hash> {
        if index >= self.count() { return Ok([0; 32]); }
        if let Leaves::Packed(packed) = self.leaves {
            let start = index as u128 * 32;
            let mut chunk = [0; 32];
            for (offset, byte) in chunk.iter_mut().enumerate() {
                let at = start + offset as u128;
                *byte = match packed {
                    Packed::Bytes(data) => if at < data.len() as u128 { data[at as usize] } else { 0 },
                    Packed::Bits(bits) => if at < bits.bytes().len() as u128 { bits.byte(at as usize) } else { 0 },
                    Packed::Scalar { value, width } => if at < width as u128 { value.byte_le(at as usize) } else { 0 },
                    Packed::Basic { values, width } => {
                        if at >= values.len() as u128 * width as u128 { 0 }
                        else {
                            let position = (at / width as u128) as usize;
                            let within = (at % width as u128) as usize;
                            match values[position] {
                                Value::Bool(bit) => u8::from(bit),
                                Value::Uint(number) => number.byte_le(within),
                                _ => return Err(Error::new(Reason::WrongType)),
                            }
                        }
                    }
                };
            }
            Ok(chunk)
        } else if let Some((desc, value)) = self.nested(index) {
            hash_tree_root(&desc, &value, arena)
        } else {
            Ok([0; 32])
        }
    }
}

/// Root every implemented SSZ type, including progressive shapes and unions.
/// Primitive root eligibility is not restricted by composite serialization's
/// 2^32-byte offset bound; neither are progressive roots count-limit checked.
pub fn hash_tree_root<'a>(desc: &Desc<'a>, value: &Value<'a>, arena: &mut Arena<'a>) -> Result<'a, Hash> {
    let layout = layout(desc, value, arena)?;
    let root = if let Some(limit) = layout.limit {
        let mut tree = Accumulator::new();
        for i in 0..layout.count() { tree.push(layout.leaf_root(i, arena)?)?; }
        tree.finish(Some(limit))?
    } else {
        let mut tree = ProgressiveAccumulator::new();
        for i in 0..layout.count() { tree.push(layout.leaf_root(i, arena)?)?; }
        tree.finish()
    };
    Ok(match layout.mixin {
        Some(word) => merkle::mix_in(&root, &word),
        None => root,
    })
}
