use core::cmp::Ordering;

use crate::{Arena, Bits, Desc, Error, Field, Nat, Reason, Result, Value};

/// Validate the declaration independently of any value or native output buffer.
pub fn validate<'a>(desc: &Desc<'a>, arena: &mut Arena<'a>) -> Result<'a, ()> {
    match desc {
        Desc::Uint(width) => match width.to_u64() {
            Some(1 | 2 | 4 | 8 | 16 | 32) => Ok(()),
            _ => Err(Error::one(Reason::UintWidth, *width)),
        },
        Desc::ByteVector(length) | Desc::BitVector(length) => {
            if length.is_zero() {
                Err(Error::new(Reason::VectorEmpty))
            } else {
                Ok(())
            }
        }
        Desc::Vector(element, length) => {
            if length.is_zero() {
                return Err(Error::new(Reason::VectorEmpty));
            }
            validate(element, arena)
        }
        Desc::List(element, _) | Desc::ProgressiveList(element, _) => validate(element, arena),
        Desc::Container(fields) => validate_fields(fields, arena),
        Desc::ProgressiveContainer { active, fields } => {
            let Some(last) = active.last() else {
                return Err(Error::new(Reason::LayoutWidth));
            };
            if !last {
                return Err(Error::new(Reason::LayoutTrailingGap));
            }
            if active.len() > 256 {
                return Err(Error::two(
                    Reason::LayoutTooWide,
                    Nat::from_u128(active.len() as u128, arena)?,
                    Nat::Small(256),
                ));
            }
            if fields.is_empty() {
                return Err(Error::new(Reason::ContainerEmpty));
            }
            let count = active.iter().filter(|present| **present).count();
            if count != fields.len() {
                return Err(Error::two(
                    Reason::LayoutFieldCount,
                    Nat::from_u128(count as u128, arena)?,
                    Nat::from_u128(fields.len() as u128, arena)?,
                ));
            }
            validate_fields(fields, arena)
        }
        Desc::CompatibleUnion(options) => {
            if options.is_empty() {
                return Err(Error::new(Reason::UnionEmpty));
            }
            // The first entry repeated later wins, not the first repeated occurrence.
            for (index, option) in options.iter().enumerate() {
                if options[index + 1..]
                    .iter()
                    .any(|later| option.selector == later.selector)
                {
                    return Err(Error::one(Reason::UnionSelectorRepeated, option.selector));
                }
            }
            for option in *options {
                if option.selector < Nat::ONE || option.selector > Nat::Small(127) {
                    return Err(Error::three(
                        Reason::UnionSelectorRange,
                        option.selector,
                        Nat::ONE,
                        Nat::Small(127),
                    ));
                }
            }
            for option in *options {
                validate(option.desc, arena)?;
            }
            // Compatibility is not transitive: every pair must be checked in order.
            for (index, option) in options.iter().enumerate() {
                for later in &options[index + 1..] {
                    if !compatible(option.desc, later.desc) {
                        return Err(Error::two(
                            Reason::UnionIncompatible,
                            option.selector,
                            later.selector,
                        ));
                    }
                }
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

fn validate_fields<'a>(fields: &[Field<'a>], arena: &mut Arena<'a>) -> Result<'a, ()> {
    if fields.is_empty() {
        return Err(Error::new(Reason::ContainerEmpty));
    }
    // Names and declarations are paired by Field, so mismatched list lengths
    // cannot be represented. Duplicate names still precede every child error.
    for (index, field) in fields.iter().enumerate() {
        if fields[index + 1..].iter().any(|later| field.name == later.name) {
            return Err(Error::new(Reason::BadDeclaration));
        }
    }
    for field in fields {
        validate(field.desc, arena)?;
    }
    Ok(())
}

/// Whether the encoded size is independent of the value, without calculating it.
pub fn is_fixed(desc: &Desc<'_>) -> bool {
    match desc {
        Desc::Bool | Desc::Uint(_) | Desc::ByteVector(_) | Desc::BitVector(_) => true,
        Desc::Vector(element, _) => is_fixed(element),
        Desc::Container(fields) | Desc::ProgressiveContainer { fields, .. } => {
            fields.iter().all(|field| is_fixed(field.desc))
        }
        _ => false,
    }
}

/// Exact fixed byte count; arbitrarily large logical sizes remain natural numbers.
pub fn fixed_size<'a>(desc: &Desc<'a>, arena: &mut Arena<'a>) -> Result<'a, Option<Nat<'a>>> {
    // A variable field makes the answer None, even when measuring an earlier
    // fixed field would require more scratch than the caller supplied.
    if !is_fixed(desc) {
        return Ok(None);
    }
    measure_fixed(desc, arena)
}

fn measure_fixed<'a>(desc: &Desc<'a>, arena: &mut Arena<'a>) -> Result<'a, Option<Nat<'a>>> {
    let width = match desc {
        Desc::Bool => Nat::ONE,
        Desc::Uint(width) => *width,
        Desc::ByteVector(length) => *length,
        Desc::BitVector(length) => {
            let (bytes, remainder) = length.div_rem_small(8, arena)?;
            if remainder == 0 { bytes } else { bytes.add(Nat::ONE, arena)? }
        }
        Desc::Vector(element, length) => {
            let Some(width) = measure_fixed(element, arena)? else {
                return Ok(None);
            };
            width.mul(*length, arena)?
        }
        Desc::Container(fields) | Desc::ProgressiveContainer { fields, .. } => {
            let mut total = Nat::ZERO;
            for field in *fields {
                let Some(width) = measure_fixed(field.desc, arena)? else {
                    return Ok(None);
                };
                total = total.add(width, arena)?;
            }
            total
        }
        _ => return Ok(None),
    };
    Ok(Some(width))
}

/// Check value shape, exact counts, capacities, and integer ranges without scratch.
pub fn fits(desc: &Desc<'_>, value: &Value<'_>) -> bool {
    match (desc, value) {
        (Desc::Bool, Value::Bool(_)) => true,
        (Desc::Uint(width), Value::Uint(number)) => {
            // n < 2^(8*width), without constructing the power or narrowing width.
            let bits = number.bit_len();
            width.cmp_u128(bits / 8 + u128::from(bits % 8 != 0)) != Ordering::Less
        }
        (Desc::ByteVector(length), Value::Bytes(bytes)) => {
            length.cmp_usize(bytes.len()) == Ordering::Equal
        }
        (Desc::ByteList(limit), Value::Bytes(bytes)) => {
            limit.cmp_usize(bytes.len()) != Ordering::Less
        }
        (Desc::BitVector(length), Value::Bits(bits)) => {
            length.cmp_u128(bits.len()) == Ordering::Equal
        }
        (Desc::BitList(limit), Value::Bits(bits)) => {
            limit.cmp_u128(bits.len()) != Ordering::Less
        }
        (Desc::ProgressiveBitList(limit), Value::Bits(bits)) => {
            limit.map_or(true, |bound| bound.cmp_u128(bits.len()) != Ordering::Less)
        }
        (Desc::Vector(element, length), Value::Seq(values)) => {
            length.cmp_usize(values.len()) == Ordering::Equal
                && values.iter().all(|value| fits(element, value))
        }
        (Desc::List(element, limit), Value::Seq(values)) => {
            limit.cmp_usize(values.len()) != Ordering::Less
                && values.iter().all(|value| fits(element, value))
        }
        (Desc::ProgressiveList(element, limit), Value::Seq(values)) => {
            limit.map_or(true, |bound| bound.cmp_usize(values.len()) != Ordering::Less)
                && values.iter().all(|value| fits(element, value))
        }
        (Desc::Container(fields) | Desc::ProgressiveContainer { fields, .. }, Value::Seq(values)) => {
            fields.len() == values.len()
                && fields.iter().zip(*values).all(|(field, value)| fits(field.desc, value))
        }
        (Desc::CompatibleUnion(options), Value::Union(selector, payload)) => {
            options.iter().find(|option| option.selector == *selector)
                .is_some_and(|option| fits(option.desc, payload))
        }
        _ => false,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ByteShape<'a> {
    Vector(Nat<'a>),
    List(Nat<'a>),
}

fn byte_sequence<'a>(desc: &Desc<'a>) -> Option<ByteShape<'a>> {
    match desc {
        Desc::ByteVector(length) => Some(ByteShape::Vector(*length)),
        Desc::ByteList(limit) => Some(ByteShape::List(*limit)),
        Desc::Vector(Desc::Uint(width), length) if *width == Nat::ONE => {
            Some(ByteShape::Vector(*length))
        }
        Desc::List(Desc::Uint(width), limit) if *width == Nat::ONE => {
            Some(ByteShape::List(*limit))
        }
        _ => None,
    }
}

/// Whether the declarations have compatible Merkle layouts, not equal encodings.
pub fn compatible(left: &Desc<'_>, right: &Desc<'_>) -> bool {
    if core::ptr::eq(left, right) {
        return true;
    }
    match (byte_sequence(left), byte_sequence(right)) {
        (None, None) => {}
        (left_bytes, right_bytes) => return left_bytes == right_bytes,
    }
    match (left, right) {
        (Desc::Bool, Desc::Bool) => true,
        (Desc::Uint(a), Desc::Uint(b))
        | (Desc::BitVector(a), Desc::BitVector(b))
        | (Desc::BitList(a), Desc::BitList(b)) => a == b,
        (Desc::ProgressiveBitList(_), Desc::ProgressiveBitList(_)) => true,
        (Desc::Vector(a, n), Desc::Vector(b, m))
        | (Desc::List(a, n), Desc::List(b, m)) => n == m && compatible(a, b),
        (Desc::ProgressiveList(a, _), Desc::ProgressiveList(b, _)) => compatible(a, b),
        (Desc::Container(a), Desc::Container(b)) => {
            a.len() == b.len() && a.iter().zip(*b)
                .all(|(a, b)| a.name == b.name && compatible(a.desc, b.desc))
        }
        (
            Desc::ProgressiveContainer { active: a, fields: af },
            Desc::ProgressiveContainer { active: b, fields: bf },
        ) => {
            // Structural equality outranks compatibility, even for an invalid
            // declaration with duplicated names at distinct positions.
            (a == b && equal_fields(af, bf)) || layouts_agree(a, af, b, bf)
        }
        (Desc::CompatibleUnion(a), Desc::CompatibleUnion(b)) => {
            // An identical union agrees with itself even if its options would
            // fail validation. Unequal unions compare every crossing pair.
            (a.len() == b.len() && a.iter().zip(*b).all(|(a, b)| {
                a.selector == b.selector && equal_desc(a.desc, b.desc)
            })) || a.iter().all(|a| b.iter().all(|b| compatible(a.desc, b.desc)))
        }
        _ => false,
    }
}

fn layouts_agree(
    left_active: &[bool],
    left_fields: &[Field<'_>],
    right_active: &[bool],
    right_fields: &[Field<'_>],
) -> bool {
    let left_placed = left_active.iter().enumerate()
        .filter(|(_, present)| **present).zip(left_fields);
    for ((left_position, _), left) in left_placed {
        let right_placed = right_active.iter().enumerate()
            .filter(|(_, present)| **present).zip(right_fields);
        for ((right_position, _), right) in right_placed {
            if left_position == right_position {
                if left.name != right.name || !compatible(left.desc, right.desc) {
                    return false;
                }
            } else if left.name == right.name {
                return false;
            }
        }
    }
    true
}

fn equal_fields(left: &[Field<'_>], right: &[Field<'_>]) -> bool {
    left.len() == right.len() && left.iter().zip(right)
        .all(|(left, right)| left.name == right.name && equal_desc(left.desc, right.desc))
}

fn equal_desc(left: &Desc<'_>, right: &Desc<'_>) -> bool {
    if core::ptr::eq(left, right) {
        return true;
    }
    match (left, right) {
        (Desc::Bool, Desc::Bool) => true,
        (Desc::Uint(a), Desc::Uint(b))
        | (Desc::ByteVector(a), Desc::ByteVector(b))
        | (Desc::ByteList(a), Desc::ByteList(b))
        | (Desc::BitVector(a), Desc::BitVector(b))
        | (Desc::BitList(a), Desc::BitList(b)) => a == b,
        (Desc::ProgressiveBitList(a), Desc::ProgressiveBitList(b)) => a == b,
        (Desc::Vector(a, n), Desc::Vector(b, m))
        | (Desc::List(a, n), Desc::List(b, m)) => n == m && equal_desc(a, b),
        (Desc::ProgressiveList(a, n), Desc::ProgressiveList(b, m)) => n == m && equal_desc(a, b),
        (Desc::Container(a), Desc::Container(b)) => equal_fields(a, b),
        (
            Desc::ProgressiveContainer { active: a, fields: af },
            Desc::ProgressiveContainer { active: b, fields: bf },
        ) => a == b && equal_fields(af, bf),
        (Desc::CompatibleUnion(a), Desc::CompatibleUnion(b)) => {
            a.len() == b.len() && a.iter().zip(*b)
                .all(|(a, b)| a.selector == b.selector && equal_desc(a.desc, b.desc))
        }
        _ => false,
    }
}

fn has_default(desc: &Desc<'_>) -> bool {
    match desc {
        Desc::CompatibleUnion(_) => false,
        // Even a zero-length vector asks for its element's default first.
        Desc::Vector(element, _) => has_default(element),
        Desc::Container(fields) | Desc::ProgressiveContainer { fields, .. } => {
            fields.iter().all(|field| has_default(field.desc))
        }
        // Empty variable collections never ask for an element default.
        _ => true,
    }
}

/// Build the upstream default into caller-owned scratch. Unions have no default.
pub fn default_value<'a>(desc: &Desc<'a>, arena: &mut Arena<'a>) -> Result<'a, Value<'a>> {
    if !has_default(desc) {
        return Err(Error::new(Reason::WrongType));
    }
    build_default(desc, arena)
}

fn build_default<'a>(desc: &Desc<'a>, arena: &mut Arena<'a>) -> Result<'a, Value<'a>> {
    match desc {
        Desc::Bool => Ok(Value::Bool(false)),
        Desc::Uint(_) => Ok(Value::Uint(Nat::ZERO)),
        Desc::ByteVector(length) => {
            let count = length.to_usize().ok_or(Error::new(Reason::ScratchExhausted))?;
            Ok(Value::Bytes(arena.bytes_with(count, |_| 0)?))
        }
        Desc::BitVector(length) => {
            let bits = length.to_u128().ok_or(Error::new(Reason::ScratchExhausted))?;
            let bytes = bits / 8 + u128::from(bits % 8 != 0);
            let count = usize::try_from(bytes).map_err(|_| Error::new(Reason::ScratchExhausted))?;
            Ok(Value::Bits(Bits::new(arena.bytes_with(count, |_| 0)?, bits)?))
        }
        Desc::ByteList(_) => Ok(Value::Bytes(&[])),
        Desc::BitList(_) | Desc::ProgressiveBitList(_) => Ok(Value::Bits(Bits::new(&[], 0)?)),
        Desc::List(_, _) | Desc::ProgressiveList(_, _) => Ok(Value::Seq(&[])),
        Desc::Vector(element, length) => {
            let one = build_default(element, arena)?;
            let count = length.to_usize().ok_or(Error::new(Reason::ScratchExhausted))?;
            Ok(Value::Seq(arena.slice_with(count, |_, _| Ok(one))?))
        }
        Desc::Container(fields) | Desc::ProgressiveContainer { fields, .. } => {
            Ok(Value::Seq(arena.slice_with(fields.len(), |index, arena| {
                build_default(fields[index].desc, arena)
            })?))
        }
        Desc::CompatibleUnion(_) => Err(Error::new(Reason::WrongType)),
    }
}

/// Compare with the default without allocating it, preserving default failure first.
pub fn is_zero<'a>(
    desc: &Desc<'a>,
    value: &Value<'a>,
    _arena: &mut Arena<'a>,
) -> Result<'a, bool> {
    if !has_default(desc) {
        return Err(Error::new(Reason::WrongType));
    }
    Ok(equals_default(desc, value))
}

fn equals_default(desc: &Desc<'_>, value: &Value<'_>) -> bool {
    match (desc, value) {
        (Desc::Bool, Value::Bool(value)) => !value,
        (Desc::Uint(_), Value::Uint(value)) => value.is_zero(),
        (Desc::ByteVector(length), Value::Bytes(bytes)) => {
            length.cmp_usize(bytes.len()) == Ordering::Equal && bytes.iter().all(|byte| *byte == 0)
        }
        (Desc::BitVector(length), Value::Bits(bits)) => {
            length.cmp_u128(bits.len()) == Ordering::Equal
                && (0..bits.bytes().len()).all(|index| bits.byte(index) == 0)
        }
        (Desc::ByteList(_), Value::Bytes(bytes)) => bytes.is_empty(),
        (Desc::BitList(_) | Desc::ProgressiveBitList(_), Value::Bits(bits)) => bits.is_empty(),
        (Desc::List(_, _) | Desc::ProgressiveList(_, _), Value::Seq(values)) => values.is_empty(),
        (Desc::Vector(element, length), Value::Seq(values)) => {
            length.cmp_usize(values.len()) == Ordering::Equal
                && values.iter().all(|value| equals_default(element, value))
        }
        (Desc::Container(fields) | Desc::ProgressiveContainer { fields, .. }, Value::Seq(values)) => {
            fields.len() == values.len() && fields.iter().zip(*values)
                .all(|(field, value)| equals_default(field.desc, value))
        }
        _ => false,
    }
}
