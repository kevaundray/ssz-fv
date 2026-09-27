use core::{cmp::Ordering, mem::MaybeUninit, ptr, slice};

use crate::schema::{fixed_size, is_fixed};
use crate::{Arena, Bits, Desc, Error, Field, Nat, Reason, Result, Value, Variant};

const OFFSET_WIDTH: usize = 4;
const COMPOSITE_LIMIT: u64 = 1u64 << 32;

fn count(value: usize) -> Nat<'static> {
    Nat::Small(value as u64)
}

fn exact<'a>(expected: Nat<'a>, actual: usize) -> Result<'a, ()> {
    if expected.cmp_usize(actual) != Ordering::Equal {
        return Err(Error::two(Reason::Scope, expected, count(actual)));
    }
    Ok(())
}

fn bounded<'a>(limit: Option<Nat<'a>>, actual: Nat<'a>) -> Result<'a, ()> {
    if let Some(limit) = limit {
        if actual > limit {
            return Err(Error::two(Reason::Limit, limit, actual));
        }
    }
    Ok(())
}

fn composite_size<'a>(size: Nat<'a>) -> Result<'a, ()> {
    if size >= Nat::Small(COMPOSITE_LIMIT) {
        return Err(Error::one(Reason::OffsetOverflow, size));
    }
    Ok(())
}

fn host_size<'a>(size: Nat<'a>) -> Result<'a, usize> {
    size.to_usize().ok_or(Error::new(Reason::OutputTooSmall))
}

fn option<'a>(variants: &[Variant<'a>], selector: Nat<'a>) -> Result<'a, &'a Desc<'a>> {
    variants.iter().find(|variant| variant.selector == selector)
        .map(|variant| variant.desc)
        .ok_or(Error::one(Reason::UnknownSelector, selector))
}

#[derive(Clone, Copy)]
enum Parts<'a> {
    Repeated(&'a Desc<'a>),
    Fields(&'a [Field<'a>]),
}

impl<'a> Parts<'a> {
    fn desc(self, index: usize) -> &'a Desc<'a> {
        match self {
            Self::Repeated(element) => element,
            Self::Fields(fields) => fields[index].desc,
        }
    }

    fn is_fixed(self) -> bool {
        match self {
            Self::Repeated(element) => is_fixed(element),
            Self::Fields(fields) => fields.iter().all(|field| is_fixed(field.desc)),
        }
    }
}

// Only layout metadata is retained: no child encoding is ever staged or copied.
// Fixed subtrees need no layout plan and are emitted directly in field order.
#[derive(Clone, Copy)]
struct Plan<'a> {
    size: Nat<'a>,
    leading: usize,
    children: &'a [Plan<'a>],
}

impl<'a> Plan<'a> {
    fn leaf(size: Nat<'a>) -> Self {
        Self { size, leading: 0, children: &[] }
    }
}

fn measure_parts<'a>(
    parts: Parts<'a>,
    values: &[Value<'a>],
    arena: &mut Arena<'a>,
    retain: bool,
) -> Result<'a, Plan<'a>> {
    let paired = match parts {
        Parts::Repeated(_) => values.len(),
        Parts::Fields(fields) => fields.len().min(values.len()),
    };
    let all_fixed = parts.is_fixed();
    let keep = retain && !all_fixed;
    let mut leading = Nat::ZERO;
    let mut bodies = Nat::ZERO;
    let mut measure_child = |index: usize, arena: &mut Arena<'a>| {
        let desc = parts.desc(index);
        let child = measure(desc, &values[index], arena, keep)?;
        let inline = match parts {
            Parts::Repeated(_) => all_fixed,
            Parts::Fields(_) => is_fixed(desc),
        };
        if inline {
            leading = leading.add(child.size, arena)?;
        } else {
            leading = leading.add(Nat::Small(OFFSET_WIDTH as u64), arena)?;
            bodies = bodies.add(child.size, arena)?;
        }
        Ok(child)
    };
    let children = if keep {
        arena.slice_with(paired, &mut measure_child)?
    } else {
        for index in 0..paired {
            measure_child(index, arena)?;
        }
        &[]
    };
    // serializeFields visits the paired prefix before refusing a count mismatch.
    if let Parts::Fields(fields) = parts {
        if fields.len() != values.len() {
            return Err(Error::new(Reason::WrongType));
        }
    }
    let size = leading.add(bodies, arena)?;
    // All children have been checked before assemble checks the total, even when
    // an earlier partial sum already exceeded the offset range.
    composite_size(size)?;
    Ok(Plan { size, leading: host_size(leading)?, children })
}

fn measure<'a>(
    desc: &Desc<'a>,
    value: &Value<'a>,
    arena: &mut Arena<'a>,
    retain: bool,
) -> Result<'a, Plan<'a>> {
    let size = match (desc, value) {
        (Desc::Bool, Value::Bool(_)) => Nat::ONE,
        (Desc::Uint(width), Value::Uint(number)) => {
            let bits = number.bit_len();
            let required = bits / 8 + u128::from(bits % 8 != 0);
            if width.cmp_u128(required) == Ordering::Less {
                return Err(Error::new(Reason::WrongType));
            }
            *width
        }
        (Desc::ByteVector(length), Value::Bytes(bytes)) => {
            exact(*length, bytes.len())?;
            count(bytes.len())
        }
        (Desc::ByteList(limit), Value::Bytes(bytes)) => {
            bounded(Some(*limit), count(bytes.len()))?;
            count(bytes.len())
        }
        (Desc::BitVector(length), Value::Bits(bits)) => {
            if length.cmp_u128(bits.len()) != Ordering::Equal {
                return Err(Error::two(
                    Reason::Scope, *length, Nat::from_u128(bits.len(), arena)?,
                ));
            }
            count(bits.bytes().len())
        }
        (Desc::BitList(limit), Value::Bits(bits)) => {
            bounded(Some(*limit), Nat::from_u128(bits.len(), arena)?)?;
            Nat::from_u128(bits.len() / 8 + 1, arena)?
        }
        (Desc::ProgressiveBitList(limit), Value::Bits(bits)) => {
            bounded(*limit, Nat::from_u128(bits.len(), arena)?)?;
            Nat::from_u128(bits.len() / 8 + 1, arena)?
        }
        (Desc::Vector(element, length), Value::Seq(values)) => {
            exact(*length, values.len())?;
            return measure_parts(Parts::Repeated(element), values, arena, retain);
        }
        (Desc::List(element, limit), Value::Seq(values)) => {
            bounded(Some(*limit), count(values.len()))?;
            return measure_parts(Parts::Repeated(element), values, arena, retain);
        }
        (Desc::ProgressiveList(element, limit), Value::Seq(values)) => {
            bounded(*limit, count(values.len()))?;
            return measure_parts(Parts::Repeated(element), values, arena, retain);
        }
        (Desc::Container(fields), Value::Seq(values))
        | (Desc::ProgressiveContainer { fields, .. }, Value::Seq(values)) => {
            return measure_parts(Parts::Fields(fields), values, arena, retain);
        }
        (Desc::CompatibleUnion(variants), Value::Union(selector, value)) => {
            let child = measure(option(variants, *selector)?, value, arena, retain)?;
            let size = child.size.add(Nat::ONE, arena)?;
            let children = if retain && !child.children.is_empty() {
                arena.slice_with(1, |_, _| Ok(child))?
            } else {
                &[]
            };
            return Ok(Plan { size, leading: 0, children });
        }
        _ => return Err(Error::new(Reason::WrongType)),
    };
    Ok(Plan::leaf(size))
}

/// Return the exact byte count, checking values in the same order as serialization.
/// Declaration validation is deliberately a separate operation.
pub fn encoded_size<'a>(
    desc: &Desc<'a>,
    value: &Value<'a>,
    arena: &mut Arena<'a>,
) -> Result<'a, usize> {
    host_size(measure(desc, value, arena, false)?.size)
}

fn copy_bytes(out: &mut [MaybeUninit<u8>], bytes: &[u8]) {
    let destination = &mut out[..bytes.len()];
    // SAFETY: the checked destination is writable for bytes.len() bytes. Its
    // exclusive borrow excludes the live immutable source; neither has padding.
    unsafe { ptr::copy_nonoverlapping(bytes.as_ptr(), destination.as_mut_ptr().cast(), bytes.len()) };
}

fn emit_parts<'a>(
    parts: Parts<'a>,
    values: &[Value<'a>],
    plan: Option<&Plan<'a>>,
    out: &mut [MaybeUninit<u8>],
) -> Result<'a, usize> {
    let children = plan.map_or(&[][..], |plan| plan.children);
    if children.is_empty() {
        let mut position = 0;
        for (index, value) in values.iter().enumerate() {
            position += emit(parts.desc(index), value, None, &mut out[position..])?;
        }
        return Ok(position);
    }
    let mut head = 0;
    let mut body = plan.map_or(0, |plan| plan.leading);
    for (index, (value, child)) in values.iter().zip(children).enumerate() {
        let desc = parts.desc(index);
        let size = host_size(child.size)?;
        let inline = match parts {
            Parts::Repeated(_) => false,
            Parts::Fields(_) => is_fixed(desc),
        };
        if inline {
            emit(desc, value, Some(child), &mut out[head..head + size])?;
            head += size;
        } else {
            copy_bytes(&mut out[head..head + OFFSET_WIDTH], &(body as u32).to_le_bytes());
            head += OFFSET_WIDTH;
            emit(desc, value, Some(child), &mut out[body..body + size])?;
            body += size;
        }
    }
    Ok(body)
}

fn emit<'a>(
    desc: &Desc<'a>,
    value: &Value<'a>,
    plan: Option<&Plan<'a>>,
    out: &mut [MaybeUninit<u8>],
) -> Result<'a, usize> {
    match (desc, value) {
        (Desc::Bool, Value::Bool(value)) => {
            out[0].write(u8::from(*value));
            Ok(1)
        }
        (Desc::Uint(width), Value::Uint(number)) => {
            let width = host_size(*width)?;
            for (index, byte) in out[..width].iter_mut().enumerate() {
                byte.write(number.byte_le(index));
            }
            Ok(width)
        }
        (Desc::ByteVector(_) | Desc::ByteList(_), Value::Bytes(bytes)) => {
            copy_bytes(&mut out[..bytes.len()], bytes);
            Ok(bytes.len())
        }
        (Desc::BitVector(_), Value::Bits(bits)) => {
            let full_bytes = (bits.len() / 8) as usize;
            copy_bytes(&mut out[..full_bytes], &bits.bytes()[..full_bytes]);
            if full_bytes < bits.bytes().len() {
                out[full_bytes].write(bits.byte(full_bytes));
            }
            Ok(bits.bytes().len())
        }
        (Desc::BitList(_) | Desc::ProgressiveBitList(_), Value::Bits(bits)) => {
            let delimiter_byte = (bits.len() / 8) as usize;
            let delimiter_bit = (bits.len() % 8) as u32;
            copy_bytes(&mut out[..delimiter_byte], &bits.bytes()[..delimiter_byte]);
            let last = if delimiter_bit == 0 { 1 } else { bits.byte(delimiter_byte) | (1 << delimiter_bit) };
            out[delimiter_byte].write(last);
            Ok(delimiter_byte + 1)
        }
        (Desc::Vector(element, _) | Desc::List(element, _)
            | Desc::ProgressiveList(element, _), Value::Seq(values)) => {
            emit_parts(Parts::Repeated(element), values, plan, out)
        }
        (Desc::Container(fields) | Desc::ProgressiveContainer { fields, .. }, Value::Seq(values)) => {
            emit_parts(Parts::Fields(fields), values, plan, out)
        }
        (Desc::CompatibleUnion(variants), Value::Union(selector, value)) => {
            out[0].write(selector.byte_le(0));
            let child = plan.and_then(|plan| plan.children.first());
            Ok(1 + emit(option(variants, *selector)?, value, child, &mut out[1..])?)
        }
        _ => Err(Error::new(Reason::WrongType)),
    }
}

/// Encode into caller-owned output, using bulk copies for complete bitfield bytes.
/// The output may be uninitialized. Success initializes exactly the returned
/// prefix; no output byte is read, and bytes beyond that prefix are unchanged.
pub fn serialize<'a>(
    desc: &Desc<'a>,
    value: &Value<'a>,
    out: &mut [MaybeUninit<u8>],
    arena: &mut Arena<'a>,
) -> Result<'a, usize> {
    let plan = measure(desc, value, arena, true)?;
    let size = host_size(plan.size)?;
    if out.len() < size {
        return Err(Error::new(Reason::OutputTooSmall));
    }
    emit(desc, value, Some(&plan), &mut out[..size])
}

/// Allocate only the final encoding and its layout metadata in caller scratch.
pub fn serialize_alloc<'a>(
    desc: &Desc<'a>,
    value: &Value<'a>,
    arena: &mut Arena<'a>,
) -> Result<'a, &'a [u8]> {
    let plan = measure(desc, value, arena, true)?;
    let size = host_size(plan.size)?;
    let out = arena.mutable_slice(size, MaybeUninit::<u8>::uninit())?;
    emit(desc, value, Some(&plan), out)?;
    // SAFETY: successful emission initializes the complete planned prefix;
    // MaybeUninit<u8> and u8 have identical layout, and arena storage lives for 'a.
    Ok(unsafe { slice::from_raw_parts(out.as_ptr().cast(), size) })
}

fn read_offset(data: &[u8], position: usize) -> usize {
    u32::from_le_bytes([
        data[position], data[position + 1], data[position + 2], data[position + 3],
    ]) as usize
}

// The entire table is validated before any element sees its byte window.
// In particular, a descending pair outranks a final offset past the scope.
fn validate_offsets<'a>(data: &[u8], count: usize) -> Result<'a, ()> {
    if count == 0 {
        return Ok(());
    }
    let mut previous = read_offset(data, 0);
    for index in 1..count {
        let next = read_offset(data, index * OFFSET_WIDTH);
        if next < previous {
            return Err(Error::new(Reason::OffsetUnordered));
        }
        previous = next;
    }
    if previous > data.len() {
        return Err(Error::new(Reason::OffsetPastScope));
    }
    Ok(())
}

fn decode_fixed<'a>(
    element: &Desc<'a>,
    count: usize,
    width: usize,
    data: &'a [u8],
    arena: &mut Arena<'a>,
) -> Result<'a, Value<'a>> {
    Ok(Value::Seq(arena.slice_with(count, |index, arena| {
        let start = index * width;
        deserialize(element, &data[start..start + width], arena)
    })?))
}

fn decode_offsets<'a>(
    element: &Desc<'a>,
    count: usize,
    data: &'a [u8],
    arena: &mut Arena<'a>,
) -> Result<'a, Value<'a>> {
    validate_offsets(data, count)?;
    Ok(Value::Seq(arena.slice_with(count, |index, arena| {
        let start = read_offset(data, index * OFFSET_WIDTH);
        let end = if index + 1 == count {
            data.len()
        } else {
            read_offset(data, (index + 1) * OFFSET_WIDTH)
        };
        deserialize(element, &data[start..end], arena)
    })?))
}

fn decode_vector<'a>(
    element: &Desc<'a>,
    length: Nat<'a>,
    data: &'a [u8],
    arena: &mut Arena<'a>,
) -> Result<'a, Value<'a>> {
    composite_size(count(data.len()))?;
    if let Some(width) = fixed_size(element, arena)? {
        exact(width.mul(length, arena)?, data.len())?;
        if length.is_zero() {
            return Ok(Value::Seq(&[]));
        }
        let length = length.to_usize().ok_or(Error::new(Reason::ScratchExhausted))?;
        let width = width.to_usize().ok_or(Error::new(Reason::ScratchExhausted))?;
        decode_fixed(element, length, width, data, arena)
    } else {
        let leading = length.mul(Nat::Small(OFFSET_WIDTH as u64), arena)?;
        if leading.cmp_usize(data.len()) == Ordering::Greater {
            return Err(Error::two(Reason::ScopeTooSmall, leading, count(data.len())));
        }
        if length.is_zero() {
            // The raw Lean decoder accepts this even for a nonempty scope;
            // rejecting a zero-length declaration belongs to schema validation.
            return Ok(Value::Seq(&[]));
        }
        let length = length.to_usize().ok_or(Error::new(Reason::ScratchExhausted))?;
        let first = read_offset(data, 0);
        if leading.cmp_usize(first) != Ordering::Equal {
            return Err(Error::two(Reason::FirstOffset, leading, count(first)));
        }
        decode_offsets(element, length, data, arena)
    }
}

fn decode_list<'a>(
    element: &Desc<'a>,
    limit: Option<Nat<'a>>,
    data: &'a [u8],
    arena: &mut Arena<'a>,
) -> Result<'a, Value<'a>> {
    composite_size(count(data.len()))?;
    if data.is_empty() {
        return Ok(Value::Seq(&[]));
    }
    if let Some(width) = fixed_size(element, arena)? {
        if width.is_zero() {
            return Err(Error::new(Reason::ScopeWidthless));
        }
        if width.cmp_usize(data.len()) == Ordering::Greater {
            return Err(Error::two(Reason::ScopeUndivided, count(data.len()), width));
        }
        let width = width.to_usize().ok_or(Error::new(Reason::BadRepresentation))?;
        if data.len() % width != 0 {
            return Err(Error::two(Reason::ScopeUndivided, count(data.len()), count(width)));
        }
        let length = data.len() / width;
        bounded(limit, count(length))?;
        decode_fixed(element, length, width, data, arena)
    } else {
        if data.len() < OFFSET_WIDTH {
            return Err(Error::two(
                Reason::ScopeTooSmall, count(OFFSET_WIDTH), count(data.len()),
            ));
        }
        let first = read_offset(data, 0);
        if first < OFFSET_WIDTH {
            return Err(Error::new(Reason::OffsetBelowTable));
        }
        if first % OFFSET_WIDTH != 0 {
            return Err(Error::new(Reason::OffsetUnaligned));
        }
        if first > data.len() {
            return Err(Error::new(Reason::OffsetPastScope));
        }
        let length = first / OFFSET_WIDTH;
        bounded(limit, count(length))?;
        decode_offsets(element, length, data, arena)
    }
}

#[derive(Clone, Copy)]
struct Slot<'a> {
    width: Option<Nat<'a>>,
    start: usize,
    end: usize,
}

fn decode_struct<'a>(
    fields: &[Field<'a>],
    data: &'a [u8],
    arena: &mut Arena<'a>,
) -> Result<'a, Value<'a>> {
    composite_size(count(data.len()))?;
    let slots = arena.mutable_slice(fields.len(), Slot { width: None, start: 0, end: 0 })?;
    let mut leading = Nat::ZERO;
    let mut all_fixed = true;
    for (field, slot) in fields.iter().zip(slots.iter_mut()) {
        slot.width = fixed_size(field.desc, arena)?;
        let width = match slot.width {
            Some(width) => width,
            None => {
                all_fixed = false;
                Nat::Small(OFFSET_WIDTH as u64)
            }
        };
        leading = leading.add(width, arena)?;
    }
    if all_fixed {
        exact(leading, data.len())?;
    } else if leading.cmp_usize(data.len()) == Ordering::Greater {
        return Err(Error::two(Reason::ScopeTooSmall, leading, count(data.len())));
    }
    let mut position = 0usize;
    for slot in slots.iter_mut() {
        let width = match slot.width {
            Some(width) => width.to_usize().ok_or(Error::new(Reason::Truncated))?,
            None => OFFSET_WIDTH,
        };
        let end = position.checked_add(width).ok_or(Error::new(Reason::Truncated))?;
        if end > data.len() {
            return Err(Error::new(Reason::Truncated));
        }
        if slot.width.is_some() {
            slot.start = position;
            slot.end = end;
        } else {
            slot.start = read_offset(data, position);
        }
        position = end;
    }
    let mut previous: Option<usize> = None;
    for index in 0..slots.len() {
        if slots[index].width.is_none() {
            if let Some(previous) = previous {
                if slots[index].start < slots[previous].start {
                    return Err(Error::new(Reason::OffsetUnordered));
                }
                slots[previous].end = slots[index].start;
            } else if slots[index].start != position {
                return Err(Error::two(
                    Reason::FirstOffset, count(position), count(slots[index].start),
                ));
            }
            previous = Some(index);
        }
    }
    if let Some(last) = previous {
        if slots[last].start > data.len() {
            return Err(Error::new(Reason::OffsetPastScope));
        }
        slots[last].end = data.len();
    } else {
        exact(count(position), data.len())?;
    }
    Ok(Value::Seq(arena.slice_with(fields.len(), |index, arena| {
        let slot = slots[index];
        deserialize(fields[index].desc, &data[slot.start..slot.end], arena)
    })?))
}

fn decode_delimited<'a>(
    limit: Option<Nat<'a>>,
    data: &'a [u8],
    arena: &mut Arena<'a>,
) -> Result<'a, Value<'a>> {
    let final_byte = *data.last().ok_or(Error::new(Reason::EmptyEncoding))?;
    if final_byte == 0 {
        return Err(Error::new(if data.iter().all(|byte| *byte == 0) {
            Reason::NoDelimiter
        } else {
            Reason::TrailingZeros
        }));
    }
    let highest = 7 - final_byte.leading_zeros();
    let length = (data.len() - 1) as u128 * 8 + u128::from(highest);
    bounded(limit, Nat::from_u128(length, arena)?)?;
    // A byte-aligned delimiter occupies a byte not belonging to the value.
    // Otherwise Bits masks it as an unused high bit, without copying the input.
    let bytes = if highest == 0 { &data[..data.len() - 1] } else { data };
    Ok(Value::Bits(Bits::new(bytes, length)?))
}

/// Decode exactly this byte scope, borrowing byte/bit payloads from input and
/// using caller scratch for layout metadata, sequence nodes, and integer limbs.
pub fn deserialize<'a>(
    desc: &Desc<'a>,
    data: &'a [u8],
    arena: &mut Arena<'a>,
) -> Result<'a, Value<'a>> {
    match desc {
        Desc::Bool => {
            exact(Nat::ONE, data.len())?;
            match data[0] {
                0 => Ok(Value::Bool(false)),
                1 => Ok(Value::Bool(true)),
                byte => Err(Error::one(Reason::NotABit, Nat::Small(u64::from(byte)))),
            }
        }
        Desc::Uint(width) => {
            exact(*width, data.len())?;
            Ok(Value::Uint(Nat::from_le_bytes(data, arena)?))
        }
        Desc::ByteVector(length) => {
            exact(*length, data.len())?;
            Ok(Value::Bytes(data))
        }
        Desc::ByteList(limit) => {
            bounded(Some(*limit), count(data.len()))?;
            Ok(Value::Bytes(data))
        }
        Desc::BitVector(length) => {
            let (whole, remainder) = length.div_rem_small(8, arena)?;
            let expected = if remainder == 0 { whole } else { whole.add(Nat::ONE, arena)? };
            exact(expected, data.len())?;
            if remainder != 0 && data.last().is_some_and(|byte| byte >> remainder != 0) {
                return Err(Error::new(Reason::PaddingBits));
            }
            let length = length.to_u128().ok_or(Error::new(Reason::BadRepresentation))?;
            Ok(Value::Bits(Bits::new(data, length)?))
        }
        Desc::BitList(limit) => decode_delimited(Some(*limit), data, arena),
        Desc::ProgressiveBitList(limit) => decode_delimited(*limit, data, arena),
        Desc::Vector(element, length) => decode_vector(element, *length, data, arena),
        Desc::List(element, limit) => decode_list(element, Some(*limit), data, arena),
        Desc::ProgressiveList(element, limit) => decode_list(element, *limit, data, arena),
        Desc::Container(fields) | Desc::ProgressiveContainer { fields, .. } => {
            decode_struct(fields, data, arena)
        }
        Desc::CompatibleUnion(variants) => {
            let selector = Nat::Small(u64::from(*data.first().ok_or(Error::new(Reason::NoSelector))?));
            let value = deserialize(option(variants, selector)?, &data[1..], arena)?;
            Ok(Value::Union(selector, arena.one(value)?))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bitfield_bulk_prefix_preserves_padding_delimiters_and_output_frame() {
        for len in [0usize, 1, 2, 3, 4, 5, 6, 7, 8, 9, 63, 64, 65, 127, 128, 129] {
            let source_len = (len + 7) / 8;
            let mut source = [0xb5u8; 17];
            if source_len != 0 {
                source[source_len - 1] = 0xff;
            }
            let bits = Bits::new(&source[..source_len], len as u128).unwrap();
            for delimited in [false, true] {
                let desc = if delimited {
                    Desc::BitList(Nat::Small(len as u64))
                } else {
                    Desc::BitVector(Nat::Small(len as u64))
                };
                let expected_len = if delimited { len / 8 + 1 } else { source_len };
                let mut expected = [0u8; 18];
                for bit in 0..len {
                    expected[bit / 8] |= ((source[bit / 8] >> (bit % 8)) & 1) << (bit % 8);
                }
                if delimited {
                    expected[len / 8] |= 1 << (len % 8);
                }
                let mut output = [MaybeUninit::new(0x7e); 24];
                let mut scratch = [];
                let mut arena = Arena::new(&mut scratch);
                let written = serialize(&desc, &Value::Bits(bits), &mut output, &mut arena).unwrap();
                assert_eq!(written, expected_len);
                for (index, byte) in output.iter().enumerate() {
                    let wanted = if index < written { expected[index] } else { 0x7e };
                    // All bytes began initialized; success initializes the prefix again.
                    assert_eq!(unsafe { byte.assume_init() }, wanted, "length {len}, byte {index}");
                }
            }
        }
    }
}
