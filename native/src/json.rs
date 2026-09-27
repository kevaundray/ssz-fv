use core::cmp::Ordering;

use crate::{codec, Arena, Desc, Error, Field, Json, Nat, Reason, Result, Spelling, Value};

const PLAIN: Spelling<'static> = Spelling::Plain(&[]);
const HEX: &[u8; 16] = b"0123456789abcdef";

fn part(spelling: Spelling<'_>, position: usize) -> Spelling<'_> {
    match spelling {
        Spelling::Plain(parts) => parts.get(position).copied().unwrap_or(PLAIN),
        Spelling::Byte => PLAIN,
    }
}

fn is_byte(spelling: Spelling<'_>) -> bool {
    matches!(spelling, Spelling::Byte)
}

fn ascii(bytes: &[u8]) -> &str {
    // Every caller constructs bytes solely from ASCII digits and punctuation.
    unsafe { core::str::from_utf8_unchecked(bytes) }
}

fn hex_with<'a>(len: usize, mut byte: impl FnMut(usize) -> u8, arena: &mut Arena<'a>) -> Result<'a, &'a str> {
    let size = len.checked_mul(2).and_then(|n| n.checked_add(2))
        .ok_or(Error::new(Reason::ScratchExhausted))?;
    let mut low = 0u8;
    let output = arena.bytes_with(size, |index| {
        if index == 0 { return b'0'; }
        if index == 1 { return b'x'; }
        if index % 2 == 0 {
            let value = byte((index - 2) / 2);
            low = value & 15;
            HEX[(value >> 4) as usize]
        } else {
            HEX[low as usize]
        }
    })?;
    Ok(ascii(output))
}

/// Write the canonical lowercase, `0x`-prefixed SSZ hexadecimal spelling.
pub fn to_hex<'a>(data: &[u8], arena: &mut Arena<'a>) -> Result<'a, &'a str> {
    hex_with(data.len(), |index| data[index], arena)
}

fn hex_digit(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

/// Read either digit case, but require the exact lowercase `0x` marker.
pub fn of_hex<'a>(text: &str, arena: &mut Arena<'a>) -> Result<'a, &'a [u8]> {
    let data = text.as_bytes();
    if !data.starts_with(b"0x") {
        return Err(Error::new(Reason::HexPrefix));
    }
    let digits = &data[2..];
    if digits.len() % 2 != 0 || digits.iter().any(|byte| hex_digit(*byte).is_none()) {
        return Err(Error::new(Reason::HexDigits));
    }
    arena.bytes_with(digits.len() / 2, |index| {
        // Both digits were validated before allocating the output.
        16 * hex_digit(digits[2 * index]).unwrap() + hex_digit(digits[2 * index + 1]).unwrap()
    })
}

fn check_uint<'a>(width: Nat<'a>, value: Nat<'a>, arena: &mut Arena<'a>) -> Result<'a, ()> {
    // Comparing bit lengths avoids materializing a huge declared upper bound.
    if !value.is_zero() && width.cmp_u128((value.bit_len() - 1) / 8) != Ordering::Greater {
        let bits = width.to_u128().unwrap() * 8;
        return Err(Error::two(Reason::UintRange, Nat::ONE.shl(bits, arena)?, value));
    }
    Ok(())
}

fn read_decimal<'a>(text: &str, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    // Lean String.toNat? permits single underscores only between ASCII digits.
    let mut last_digit = false;
    let mut separators = 0usize;
    for byte in text.bytes() {
        if byte.is_ascii_digit() {
            last_digit = true;
        } else if byte == b'_' && last_digit {
            separators += 1;
            last_digit = false;
        } else {
            return Err(Error::new(Reason::WrongType));
        }
    }
    if !last_digit {
        return Err(Error::new(Reason::WrongType));
    }
    if separators == 0 {
        return Nat::from_decimal(text, arena);
    }
    let mut digits = text.bytes().filter(|byte| *byte != b'_');
    let stripped = arena.bytes_with(text.len() - separators, |_| digits.next().unwrap())?;
    Nat::from_decimal(ascii(stripped), arena)
}

fn power_ten<'a>(exponent: Nat<'a>, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    let mut power = Nat::Small(10);
    let mut result = Nat::ONE;
    for bit in 0..exponent.bit_len() {
        if exponent.bit(bit) {
            result = result.mul(power, arena)?;
        }
        if bit + 1 < exponent.bit_len() {
            power = power.mul(power, arena)?;
        }
    }
    Ok(result)
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Number<'a> {
    pub negative: bool,
    pub mantissa: Nat<'a>,
    pub exponent: Nat<'a>,
}

/// Reconstruct Lean's signed mantissa * 10^-exponent without floating point.
/// Fractional trailing zeroes are not normalized: 1.0 retains exponent one,
/// whereas 1.0e1 has exponent zero and mantissa ten.
pub(crate) fn parse_number<'a>(text: &str, arena: &mut Arena<'a>) -> Result<'a, Number<'a>> {
    let bytes = text.as_bytes();
    let negative = bytes.first() == Some(&b'-');
    let whole_start = usize::from(negative);
    let mut cursor = whole_start;
    while cursor < bytes.len() && bytes[cursor].is_ascii_digit() {
        cursor += 1;
    }
    let whole_end = cursor;
    if whole_start == whole_end || (bytes[whole_start] == b'0' && whole_end - whole_start != 1) {
        return Err(Error::new(Reason::WrongType));
    }
    let mut fraction_start = cursor;
    let mut fraction_end = cursor;
    if bytes.get(cursor) == Some(&b'.') {
        cursor += 1;
        fraction_start = cursor;
        while cursor < bytes.len() && bytes[cursor].is_ascii_digit() {
            cursor += 1;
        }
        fraction_end = cursor;
        if fraction_start == fraction_end {
            return Err(Error::new(Reason::WrongType));
        }
    }
    let mut exponent_negative = false;
    let mut exponent_text = "0";
    if matches!(bytes.get(cursor), Some(b'e' | b'E')) {
        cursor += 1;
        exponent_negative = bytes.get(cursor) == Some(&b'-');
        if matches!(bytes.get(cursor), Some(b'-' | b'+')) {
            cursor += 1;
        }
        let start = cursor;
        while cursor < bytes.len() && bytes[cursor].is_ascii_digit() {
            cursor += 1;
        }
        if cursor == start {
            return Err(Error::new(Reason::WrongType));
        }
        exponent_text = &text[start..cursor];
    }
    if cursor != bytes.len() {
        return Err(Error::new(Reason::WrongType));
    }
    let fraction = fraction_end - fraction_start;
    let fractional_width = Nat::from_u128(fraction as u128, arena)?;
    let explicit_exponent = Nat::from_decimal(exponent_text, arena)?;
    let (exponent, shift) = if exponent_negative {
        (fractional_width.add(explicit_exponent, arena)?, Nat::ZERO)
    } else {
        (fractional_width.sub(explicit_exponent, arena)?, explicit_exponent.sub(fractional_width, arena)?)
    };
    let nonzero = bytes[whole_start..whole_end].iter()
        .chain(bytes[fraction_start..fraction_end].iter()).any(|byte| *byte != b'0');
    let mut mantissa = if !nonzero {
        Nat::ZERO
    } else if fraction == 0 {
        Nat::from_decimal(&text[whole_start..whole_end], arena)?
    } else {
        let whole_len = whole_end - whole_start;
        let digits = arena.bytes_with(whole_len + fraction, |index| {
            if index < whole_len { bytes[whole_start + index] }
            else { bytes[fraction_start + index - whole_len] }
        })?;
        Nat::from_decimal(ascii(digits), arena)?
    };
    if nonzero && !shift.is_zero() {
        mantissa = mantissa.mul(power_ten(shift, arena)?, arena)?;
    }
    Ok(Number { negative: negative && nonzero, mantissa, exponent })
}

fn read_number<'a>(text: &str, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    let number = parse_number(text, arena)?;
    if number.negative || !number.exponent.is_zero() {
        Err(Error::new(Reason::WrongType))
    } else {
        Ok(number.mantissa)
    }
}

fn read_nat<'a>(document: &Json<'a>, arena: &mut Arena<'a>) -> Result<'a, Nat<'a>> {
    match document {
        Json::String(text) => read_decimal(text, arena),
        Json::Number(text) => read_number(text, arena),
        _ => Err(Error::new(Reason::WrongType)),
    }
}

fn collection_hex<'a>(document: &Json<'a>) -> Result<'a, &'a str> {
    match document {
        Json::String(text) => Ok(text),
        Json::Array(_) => Err(Error::new(Reason::ElementKind)),
        _ => Err(Error::new(Reason::WrongType)),
    }
}

fn json_sequence<'a>(element: &Desc<'a>, spelling: Spelling<'a>, values: &[Value<'a>], arena: &mut Arena<'a>) -> Result<'a, Json<'a>> {
    if is_byte(spelling) {
        for value in values {
            match value {
                Value::Uint(n) if *n < Nat::Small(256) => (),
                Value::Uint(n) => return Err(Error::two(Reason::UintRange, Nat::Small(256), *n)),
                _ => return Err(Error::new(Reason::WrongType)),
            }
        }
        return Ok(Json::String(hex_with(values.len(), |index| {
            match values[index] { Value::Uint(n) => n.byte_le(0), _ => unreachable!() }
        }, arena)?));
    }
    Ok(Json::Array(arena.slice_with(values.len(), |index, arena| {
        json_of(element, spelling, &values[index], arena)
    })?))
}

fn json_fields<'a>(fields: &[Field<'a>], spelling: Spelling<'a>, values: &[Value<'a>], arena: &mut Arena<'a>) -> Result<'a, Json<'a>> {
    // jsonOfFields visits the common prefix before rejecting an arity mismatch.
    let entries = arena.mutable_slice_with(fields.len().min(values.len()), |index, arena| {
        Ok((fields[index].name, json_of(fields[index].desc, part(spelling, index), &values[index], arena)?))
    })?;
    if fields.len() != values.len() {
        return Err(Error::new(Reason::WrongType));
    }
    // A well-formed descriptor has unique names; Lean's object map enumerates
    // them lexicographically, independently of declaration/validation order.
    entries.sort_unstable_by(|left, right| left.0.cmp(right.0));
    Ok(Json::Object(entries))
}

/// Apply the upstream raw-value JSON writer, without imposing an extra fits check.
pub fn json_of<'a>(desc: &Desc<'a>, spelling: Spelling<'a>, value: &Value<'a>, arena: &mut Arena<'a>) -> Result<'a, Json<'a>> {
    match (desc, value) {
        (Desc::Bool, Value::Bool(value)) => Ok(Json::Bool(*value)),
        (Desc::Uint(width), Value::Uint(value)) => {
            check_uint(*width, *value, arena)?;
            if is_byte(spelling) && *width == Nat::ONE {
                Ok(Json::String(hex_with(1, |_| value.byte_le(0), arena)?))
            } else {
                Ok(Json::String(value.decimal(arena)?))
            }
        }
        (Desc::ByteVector(_) | Desc::ByteList(_), Value::Bytes(data)) => Ok(Json::String(to_hex(data, arena)?)),
        (Desc::BitVector(_) | Desc::BitList(_) | Desc::ProgressiveBitList(_), Value::Bits(_)) => {
            let data = codec::serialize_alloc(desc, value, arena)?;
            Ok(Json::String(to_hex(data, arena)?))
        }
        (Desc::Vector(element, _) | Desc::List(element, _) | Desc::ProgressiveList(element, _), Value::Seq(values)) => {
            json_sequence(element, part(spelling, 0), values, arena)
        }
        (Desc::Container(fields) | Desc::ProgressiveContainer { fields, .. }, Value::Seq(values)) => {
            json_fields(fields, spelling, values, arena)
        }
        (Desc::CompatibleUnion(options), Value::Union(selector, data)) => {
            let (position, option) = options.iter().enumerate().find(|(_, option)| option.selector == *selector)
                .ok_or(Error::one(Reason::UnknownSelector, *selector))?;
            let selector = Json::String(selector.decimal(arena)?);
            let data = json_of(option.desc, part(spelling, position), data, arena)?;
            Ok(Json::Object(arena.copy(&[("data", data), ("selector", selector)])?))
        }
        _ => Err(Error::new(Reason::WrongType)),
    }
}

fn value_sequence<'a>(element: &Desc<'a>, spelling: Spelling<'a>, document: &Json<'a>, arena: &mut Arena<'a>) -> Result<'a, &'a [Value<'a>]> {
    if is_byte(spelling) {
        let data = of_hex(collection_hex(document)?, arena)?;
        return arena.slice_with(data.len(), |index, _| Ok(Value::Uint(Nat::Small(data[index] as u64))));
    }
    let Json::Array(entries) = document else { return Err(Error::new(Reason::WrongType)); };
    arena.slice_with(entries.len(), |index, arena| value_of(element, spelling, &entries[index], arena))
}

pub(crate) fn object_value<'d, 'a>(object: &'d [(&'a str, Json<'a>)], name: &str) -> Option<&'d Json<'a>> {
    // Lean Json.mkObj and the parser both insert left-to-right: last duplicate wins.
    object.iter().rev().find(|(key, _)| *key == name).map(|(_, value)| value)
}

fn value_fields<'a>(fields: &[Field<'a>], spelling: Spelling<'a>, document: &Json<'a>, arena: &mut Arena<'a>) -> Result<'a, Value<'a>> {
    let Json::Object(object) = document else { return Err(Error::new(Reason::StructNotAnObject)); };
    let extra = object.iter().map(|(key, _)| *key)
        .filter(|key| !fields.iter().any(|field| field.name == *key)).min();
    if let Some(name) = extra {
        return Err(Error::named(Reason::UndeclaredField, name));
    }
    Ok(Value::Seq(arena.slice_with(fields.len(), |index, arena| {
        let field = fields[index];
        let entry = object_value(object, field.name).ok_or(Error::named(Reason::MissingField, field.name))?;
        value_of(field.desc, part(spelling, index), entry, arena)
    })?))
}

/// Read an already-parsed semantic JSON document under the SSZ mapping.
pub fn value_of<'a>(desc: &Desc<'a>, spelling: Spelling<'a>, document: &Json<'a>, arena: &mut Arena<'a>) -> Result<'a, Value<'a>> {
    match desc {
        Desc::Bool => match document {
            Json::Bool(value) => Ok(Value::Bool(*value)),
            _ => Err(Error::new(Reason::WrongType)),
        },
        Desc::Uint(width) => {
            if is_byte(spelling) && *width == Nat::ONE {
                let Json::String(text) = document else { return Err(Error::new(Reason::WrongType)); };
                let data = of_hex(text, arena)?;
                if data.len() != 1 {
                    return Err(Error::two(Reason::HexLength, Nat::ONE, Nat::from_u128(data.len() as u128, arena)?));
                }
                return Ok(Value::Uint(Nat::Small(data[0] as u64)));
            }
            let value = read_nat(document, arena)?;
            check_uint(*width, value, arena)?;
            Ok(Value::Uint(value))
        }
        Desc::ByteVector(length) | Desc::ByteList(length) => {
            let data = of_hex(collection_hex(document)?, arena)?;
            let mismatch = match desc {
                Desc::ByteVector(_) => length.cmp_usize(data.len()) != Ordering::Equal,
                _ => length.cmp_usize(data.len()) == Ordering::Less,
            };
            if mismatch {
                let reason = if matches!(desc, Desc::ByteVector(_)) { Reason::HexLength } else { Reason::OverLimit };
                return Err(Error::two(reason, *length, Nat::from_u128(data.len() as u128, arena)?));
            }
            Ok(Value::Bytes(data))
        }
        Desc::BitVector(_) | Desc::BitList(_) | Desc::ProgressiveBitList(_) => {
            let data = of_hex(collection_hex(document)?, arena)?;
            codec::deserialize(desc, data, arena).map_err(|mut error| {
                error.reason = match error.reason {
                    Reason::PaddingBits => Reason::BitfieldPadding,
                    Reason::NoDelimiter => Reason::BitfieldDelimiter,
                    Reason::TrailingZeros => Reason::BitfieldTrailingZeros,
                    Reason::Limit => Reason::OverLimit,
                    reason => reason,
                };
                error
            })
        }
        Desc::Vector(element, length) | Desc::List(element, length) => {
            let values = value_sequence(element, part(spelling, 0), document, arena)?;
            let mismatch = match desc {
                Desc::Vector(_, _) => length.cmp_usize(values.len()) != Ordering::Equal,
                _ => length.cmp_usize(values.len()) == Ordering::Less,
            };
            if mismatch {
                let reason = if matches!(desc, Desc::Vector(_, _)) { Reason::Count } else { Reason::OverLimit };
                return Err(Error::two(reason, *length, Nat::from_u128(values.len() as u128, arena)?));
            }
            Ok(Value::Seq(values))
        }
        Desc::ProgressiveList(element, limit) => {
            let values = value_sequence(element, part(spelling, 0), document, arena)?;
            if let Some(limit) = limit {
                if limit.cmp_usize(values.len()) == Ordering::Less {
                    return Err(Error::two(Reason::OverLimit, *limit, Nat::from_u128(values.len() as u128, arena)?));
                }
            }
            Ok(Value::Seq(values))
        }
        Desc::Container(fields) | Desc::ProgressiveContainer { fields, .. } => value_fields(fields, spelling, document, arena),
        Desc::CompatibleUnion(options) => {
            let Json::Object(object) = document else { return Err(Error::new(Reason::StructNotAnObject)); };
            if object.is_empty() {
                return Err(Error::new(Reason::NoDefault));
            }
            let selector = object_value(object, "selector").ok_or(Error::named(Reason::MissingField, "selector"))?;
            let data = object_value(object, "data").ok_or(Error::named(Reason::MissingField, "data"))?;
            let selector = read_nat(selector, arena)?;
            let (position, option) = options.iter().enumerate().find(|(_, option)| option.selector == selector)
                .ok_or(Error::one(Reason::UndeclaredSelector, selector))?;
            let value = value_of(option.desc, part(spelling, position), data, arena)?;
            Ok(Value::Union(selector, arena.one(value)?))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Bits, Variant};
    use core::mem::MaybeUninit;

    #[test]
    fn numeric_tokens_preserve_lean_exponent_and_mantissa() {
        let desc = Desc::Uint(Nat::Small(32));
        for (token, expected) in [
            ("1", 1), ("1e3", 1000), ("1.20e2", 120), ("1.0e1", 10),
            ("1E+003", 1000), ("-0", 0), ("-0e3", 0), ("1e-0", 1),
            ("0e99999999999999999999999999999999999999999", 0),
            ("184467440737095516160", 184467440737095516160u128),
        ] {
            let mut storage = [MaybeUninit::uninit(); 8192];
            let mut arena = Arena::new(&mut storage);
            let expected = Nat::from_u128(expected, &mut arena).unwrap();
            assert_eq!(value_of(&desc, PLAIN, &Json::Number(token), &mut arena), Ok(Value::Uint(expected)), "{token}");
        }
        for token in ["1.0", "10e-1", "0.0", "1.0e0", "1.00e1", "-1", "0e-1", "-0.0e0"] {
            let mut storage = [MaybeUninit::uninit(); 8192];
            let mut arena = Arena::new(&mut storage);
            assert_eq!(value_of(&desc, PLAIN, &Json::Number(token), &mut arena), Err(Error::new(Reason::WrongType)), "{token}");
        }
    }

    #[test]
    fn decimal_strings_follow_lean_digit_separator_rules() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        let desc = Desc::Uint(Nat::Small(2));
        assert_eq!(value_of(&desc, PLAIN, &Json::String("01_000"), &mut arena), Ok(Value::Uint(Nat::Small(1000))));
        for text in ["", "_1", "1_", "1__0", "+1", "-0", " 1", "1.0", "１"] {
            assert_eq!(value_of(&desc, PLAIN, &Json::String(text), &mut arena), Err(Error::new(Reason::WrongType)), "{text}");
        }
        assert_eq!(value_of(&Desc::Uint(Nat::ONE), PLAIN, &Json::Number("2.56e2"), &mut arena),
            Err(Error::two(Reason::UintRange, Nat::Small(256), Nat::Small(256))));
    }

    #[test]
    fn object_lookup_and_error_order_match_sorted_maps() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        let boolean = Desc::Bool;
        let fields = [Field { name: "z", desc: &boolean }, Field { name: "a", desc: &boolean }];
        let desc = Desc::Container(&fields);
        let extras = [("unknown_z", Json::Null), ("unknown_a", Json::Null)];
        assert_eq!(value_of(&desc, PLAIN, &Json::Object(&extras), &mut arena), Err(Error::named(Reason::UndeclaredField, "unknown_a")));
        assert_eq!(value_of(&desc, PLAIN, &Json::Object(&[]), &mut arena), Err(Error::named(Reason::MissingField, "z")));
        let wrong_before_missing = [("z", Json::Null)];
        assert_eq!(value_of(&desc, PLAIN, &Json::Object(&wrong_before_missing), &mut arena), Err(Error::new(Reason::WrongType)));
        let duplicate = [("a", Json::Bool(false)), ("z", Json::Null), ("z", Json::Bool(true))];
        let values = [Value::Bool(true), Value::Bool(false)];
        assert_eq!(value_of(&desc, PLAIN, &Json::Object(&duplicate), &mut arena), Ok(Value::Seq(&values)));
        let expected = [("a", Json::Bool(false)), ("z", Json::Bool(true))];
        assert_eq!(json_of(&desc, PLAIN, &Value::Seq(&values), &mut arena), Ok(Json::Object(&expected)));
    }

    #[test]
    fn union_empty_missing_and_unknown_selector_remain_distinct() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        let boolean = Desc::Bool;
        let variants = [Variant { selector: Nat::ONE, desc: &boolean }];
        let desc = Desc::CompatibleUnion(&variants);
        assert_eq!(value_of(&desc, PLAIN, &Json::Object(&[]), &mut arena), Err(Error::new(Reason::NoDefault)));
        let no_data = [("selector", Json::Null)];
        assert_eq!(value_of(&desc, PLAIN, &Json::Object(&no_data), &mut arena), Err(Error::named(Reason::MissingField, "data")));
        let unknown = [("selector", Json::String("2")), ("data", Json::Null)];
        assert_eq!(value_of(&desc, PLAIN, &Json::Object(&unknown), &mut arena), Err(Error::one(Reason::UndeclaredSelector, Nat::Small(2))));
        let ignored = [("selector", Json::String("1")), ("data", Json::Bool(true)), ("ignored", Json::Null)];
        let payload = Value::Bool(true);
        assert_eq!(value_of(&desc, PLAIN, &Json::Object(&ignored), &mut arena), Ok(Value::Union(Nat::ONE, &payload)));
        assert_eq!(json_of(&desc, PLAIN, &Value::Union(Nat::Small(2), &payload), &mut arena), Err(Error::one(Reason::UnknownSelector, Nat::Small(2))));
    }

    #[test]
    fn raw_writer_does_not_add_collection_fits_checks() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        assert_eq!(json_of(&Desc::ByteVector(Nat::ONE), PLAIN, &Value::Bytes(&[1, 2]), &mut arena), Ok(Json::String("0x0102")));
        let boolean = Desc::Bool;
        let values = [Value::Bool(true)];
        let documents = [Json::Bool(true)];
        assert_eq!(json_of(&Desc::List(&boolean, Nat::ZERO), PLAIN, &Value::Seq(&values), &mut arena), Ok(Json::Array(&documents)));
        let uint = Desc::Uint(Nat::ONE);
        let fields = [Field { name: "x", desc: &uint }];
        let extra = [Value::Uint(Nat::Small(256)), Value::Bool(false)];
        assert_eq!(json_of(&Desc::Container(&fields), PLAIN, &Value::Seq(&extra), &mut arena), Err(Error::two(Reason::UintRange, Nat::Small(256), Nat::Small(256))));
    }

    #[test]
    fn aliases_control_hex_without_changing_plain_uints() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        let uint = Desc::Uint(Nat::ONE);
        let value = Value::Uint(Nat::Small(255));
        assert_eq!(json_of(&uint, Spelling::Byte, &value, &mut arena), Ok(Json::String("0xff")));
        assert_eq!(json_of(&uint, PLAIN, &value, &mut arena), Ok(Json::String("255")));
        let parts = [Spelling::Byte];
        let spelling = Spelling::Plain(&parts);
        let values = [Value::Uint(Nat::ONE), Value::Uint(Nat::Small(255))];
        let desc = Desc::Vector(&uint, Nat::Small(2));
        assert_eq!(json_of(&desc, spelling, &Value::Seq(&values), &mut arena), Ok(Json::String("0x01ff")));
        assert_eq!(value_of(&desc, spelling, &Json::String("0x01FF"), &mut arena), Ok(Value::Seq(&values)));
        assert_eq!(value_of(&desc, spelling, &Json::Array(&[]), &mut arena), Err(Error::new(Reason::ElementKind)));
        assert_eq!(value_of(&uint, Spelling::Byte, &Json::Array(&[]), &mut arena), Err(Error::new(Reason::WrongType)));
    }

    #[test]
    fn bitfield_codec_errors_are_remapped_selectively() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        for (desc, text, expected) in [
            (Desc::BitVector(Nat::ONE), "0x80", Error::new(Reason::BitfieldPadding)),
            (Desc::BitList(Nat::Small(8)), "0x", Error::new(Reason::EmptyEncoding)),
            (Desc::BitList(Nat::Small(8)), "0x00", Error::new(Reason::BitfieldDelimiter)),
            (Desc::BitList(Nat::Small(8)), "0x0100", Error::new(Reason::BitfieldTrailingZeros)),
            (Desc::BitList(Nat::ONE), "0x04", Error::two(Reason::OverLimit, Nat::ONE, Nat::Small(2))),
            (Desc::BitVector(Nat::ONE), "0x", Error::two(Reason::Scope, Nat::ONE, Nat::ZERO)),
        ] {
            assert_eq!(value_of(&desc, PLAIN, &Json::String(text), &mut arena), Err(expected));
        }
        let bits = Bits::new(&[5], 3).unwrap();
        let desc = Desc::ProgressiveBitList(None);
        assert_eq!(json_of(&desc, PLAIN, &Value::Bits(bits), &mut arena), Ok(Json::String("0x0d")));
        assert_eq!(value_of(&desc, PLAIN, &Json::String("0x0d"), &mut arena), Ok(Value::Bits(bits)));
    }

    #[test]
    fn child_errors_precede_sequence_count_and_capacity() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        let uint = Desc::Uint(Nat::ONE);
        let entries = [Json::String("256")];
        let desc = Desc::List(&uint, Nat::ZERO);
        assert_eq!(value_of(&desc, PLAIN, &Json::Array(&entries), &mut arena), Err(Error::two(Reason::UintRange, Nat::Small(256), Nat::Small(256))));
        let entries = [Json::String("1")];
        assert_eq!(value_of(&desc, PLAIN, &Json::Array(&entries), &mut arena), Err(Error::two(Reason::OverLimit, Nat::ZERO, Nat::ONE)));
        assert_eq!(value_of(&Desc::Vector(&uint, Nat::Small(2)), PLAIN, &Json::Array(&entries), &mut arena), Err(Error::two(Reason::Count, Nat::Small(2), Nat::ONE)));
    }

    #[test]
    fn hexadecimal_errors_keep_prefix_precedence_and_accept_empty() {
        let mut storage = [MaybeUninit::uninit(); 8192];
        let mut arena = Arena::new(&mut storage);
        assert_eq!(of_hex("0Xzz", &mut arena), Err(Error::new(Reason::HexPrefix)));
        for text in ["0x1", "0xgg", "0xé"] {
            assert_eq!(of_hex(text, &mut arena), Err(Error::new(Reason::HexDigits)));
        }
        assert_eq!(of_hex("0x", &mut arena), Ok(&[][..]));
        assert_eq!(of_hex("0xAa01", &mut arena), Ok(&[170, 1][..]));
        assert_eq!(to_hex(&[0, 15, 255], &mut arena), Ok("0x000fff"));
    }
}
