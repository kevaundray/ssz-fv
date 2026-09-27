use core::cmp::Ordering;

use crate::{Arena, Error, Reason, Result};

/// An exact natural number, with little-endian base-2^64 limbs.
///
/// Publicly supplied Large values may contain leading zero limbs. All numeric
/// operations ignore them; operation results use Small whenever they fit u64.
#[derive(Clone, Copy, Debug)]
pub enum Nat<'a> {
    Small(u64),
    Large(&'a [u64]),
}

impl<'a> Nat<'a> {
    pub const ZERO: Self = Self::Small(0);
    pub const ONE: Self = Self::Small(1);

    pub fn word_len(self) -> usize {
        match self {
            Self::Small(0) => 0,
            Self::Small(_) => 1,
            Self::Large(words) => significant_words(words),
        }
    }

    /// Return a base-2^64 digit, with zero extension outside the representation.
    pub fn word(self, index: usize) -> u64 {
        match self {
            Self::Small(value) => if index == 0 { value } else { 0 },
            Self::Large(words) => words.get(index).copied().unwrap_or(0),
        }
    }

    pub fn is_zero(self) -> bool {
        self.word_len() == 0
    }

    pub fn to_u64(self) -> Option<u64> {
        if self.word_len() <= 1 { Some(self.word(0)) } else { None }
    }

    pub fn to_usize(self) -> Option<usize> {
        usize::try_from(self.to_u64()?).ok()
    }

    pub fn to_u128(self) -> Option<u128> {
        if self.word_len() <= 2 {
            Some(self.word(0) as u128 | ((self.word(1) as u128) << 64))
        } else {
            None
        }
    }

    pub fn bit_len(self) -> u128 {
        let count = self.word_len();
        if count == 0 {
            0
        } else {
            (count as u128 - 1) * 64 + (64 - self.word(count - 1).leading_zeros()) as u128
        }
    }

    pub fn bit(self, index: u128) -> bool {
        match usize::try_from(index / 64) {
            Ok(word) => (self.word(word) >> (index % 64) as u32) & 1 != 0,
            Err(_) => false,
        }
    }

    pub fn is_power_of_two(self) -> bool {
        let mut seen = false;
        for index in 0..self.word_len() {
            let word = self.word(index);
            if word != 0 {
                if seen || !word.is_power_of_two() {
                    return false;
                }
                seen = true;
            }
        }
        seen
    }

    pub fn byte_le(self, index: usize) -> u8 {
        (self.word(index / 8) >> ((index % 8) * 8)) as u8
    }

    pub fn cmp_u128(self, other: u128) -> Ordering {
        match self.to_u128() {
            Some(value) => value.cmp(&other),
            None => Ordering::Greater,
        }
    }

    pub fn cmp_usize(self, other: usize) -> Ordering {
        self.cmp_u128(other as u128)
    }

    pub fn from_u128(value: u128, arena: &mut Arena<'a>) -> Result<'a, Self> {
        if value <= u64::MAX as u128 {
            Ok(Self::Small(value as u64))
        } else {
            Ok(Self::Large(arena.copy(&[value as u64, (value >> 64) as u64])?))
        }
    }

    /// Decode any number of little-endian bytes, including redundant high zeros.
    pub fn from_le_bytes(data: &[u8], arena: &mut Arena<'a>) -> Result<'a, Self> {
        let mut count = data.len();
        while count != 0 && data[count - 1] == 0 {
            count -= 1;
        }
        if count <= 8 {
            let mut value = 0u64;
            for (index, byte) in data[..count].iter().enumerate() {
                value |= (*byte as u64) << (index * 8);
            }
            return Ok(Self::Small(value));
        }
        let words = 1 + (count - 1) / 8;
        let limbs = arena.slice_with(words, |index, _| {
            let start = index * 8;
            let available = (count - start).min(8);
            let mut word = 0u64;
            for offset in 0..available {
                word |= (data[start + offset] as u64) << (offset * 8);
            }
            Ok(word)
        })?;
        Ok(Self::Large(limbs))
    }

    /// Parse nonempty ASCII decimal digits.
    /// Leading zeros are accepted; signs, whitespace and non-ASCII digits are not.
    pub fn from_decimal(text: &str, arena: &mut Arena<'a>) -> Result<'a, Self> {
        let digits = text.as_bytes();
        if digits.is_empty() || digits.iter().any(|byte| !byte.is_ascii_digit()) {
            return Err(Error::new(Reason::BadRepresentation));
        }
        let first = digits.iter().position(|byte| *byte != b'0').unwrap_or(digits.len());
        let digits = &digits[first..];
        let mut small = 0u64;
        let mut position = 0;
        while position < digits.len() {
            let digit = (digits[position] - b'0') as u64;
            match small.checked_mul(10).and_then(|value| value.checked_add(digit)) {
                Some(value) => small = value,
                None => break,
            }
            position += 1;
        }
        if position == digits.len() {
            return Ok(Self::Small(small));
        }
        // log2(10) < 3322/1000. The input slice bounds digits.len(), so this
        // u128 arithmetic cannot overflow on any supported Rust pointer width.
        // Round upwards for a single allocation rather than retaining every
        // intermediate multiplication in a monotonic arena.
        let bits = (digits.len() as u128 * 3322 + 999) / 1000;
        let count = usize::try_from((bits + 63) / 64)
            .map_err(|_| Error::new(Reason::ScratchExhausted))?;
        let limbs = arena.mutable_slice(count, 0u64)?;
        limbs[0] = small;
        let mut used = 1;
        while position < digits.len() {
            let end = position + (digits.len() - position).min(19);
            let mut factor = 1u64;
            let mut carry = 0u128;
            for digit in &digits[position..end] {
                factor *= 10;
                carry = carry * 10 + (*digit - b'0') as u128;
            }
            for word in &mut limbs[..used] {
                let product = *word as u128 * factor as u128 + carry;
                *word = product as u64;
                carry = product >> 64;
            }
            if carry != 0 {
                // The decimal-length bound above includes every partial value.
                limbs[used] = carry as u64;
                used += 1;
            }
            position = end;
        }
        Ok(Self::Large(&limbs[..used]))
    }

    /// Write canonical decimal digits into caller scratch, with no size cap.
    pub fn decimal(self, arena: &mut Arena<'a>) -> Result<'a, &'a str> {
        if let Some(mut value) = self.to_u64() {
            if value == 0 {
                return Ok("0");
            }
            let mut digits = [0u8; 20];
            let mut start = digits.len();
            while value != 0 {
                start -= 1;
                digits[start] = b'0' + (value % 10) as u8;
                value /= 10;
            }
            let output = arena.copy(&digits[start..])?;
            // SAFETY: every output byte was generated in the ASCII digit range.
            return Ok(unsafe { core::str::from_utf8_unchecked(output) });
        }
        let count = self.word_len();
        let words = arena.mutable_slice_with(count, |index, _| Ok(self.word(index)))?;
        // log10(2) < 30103/100000, so the bound accommodates every digit.
        let capacity = usize::try_from(self.bit_len() * 30103 / 100000 + 1)
            .map_err(|_| Error::new(Reason::ScratchExhausted))?;
        let digits = arena.mutable_slice(capacity, b'0')?;
        let mut start = capacity;
        let mut used = count;
        while used != 0 {
            let mut remainder = divide_words(&mut words[..used], 10_000_000_000_000_000_000);
            while used != 0 && words[used - 1] == 0 {
                used -= 1;
            }
            let width = if used == 0 { 0 } else { 19 };
            let mut written = 0;
            while remainder != 0 || written < width {
                start -= 1;
                digits[start] = b'0' + (remainder % 10) as u8;
                remainder /= 10;
                written += 1;
            }
        }
        // SAFETY: initialized padding and all subsequently written bytes are
        // ASCII digits; the suffix starts at the highest significant digit.
        Ok(unsafe { core::str::from_utf8_unchecked(&digits[start..]) })
    }

    pub fn add(self, rhs: Self, arena: &mut Arena<'a>) -> Result<'a, Self> {
        let left = self.word_len();
        let right = rhs.word_len();
        if left == 0 {
            return Ok(rhs.normalized());
        }
        if right == 0 {
            return Ok(self.normalized());
        }
        if left <= 1 && right <= 1 {
            return Self::from_u128(self.word(0) as u128 + rhs.word(0) as u128, arena);
        }
        let count = left.max(right);
        let allocated = count.checked_add(1).ok_or_else(scratch_exhausted)?;
        let mut carry = 0u128;
        let words = arena.slice_with(allocated, |index, _| {
            let sum = self.word(index) as u128 + rhs.word(index) as u128 + carry;
            carry = sum >> 64;
            Ok(sum as u64)
        })?;
        Ok(Self::from_words(words))
    }

    /// Natural subtraction: negative mathematical results saturate to zero.
    pub fn sub(self, rhs: Self, arena: &mut Arena<'a>) -> Result<'a, Self> {
        if self <= rhs {
            return Ok(Self::ZERO);
        }
        if rhs.is_zero() {
            return Ok(self.normalized());
        }
        let count = self.word_len();
        let (low, mut borrow) = self.word(0).overflowing_sub(rhs.word(0));
        // Delay allocation until a nonzero high digit is found. This also keeps
        // arbitrarily large cancellations that fit u64 allocation-free, without
        // computing the subtraction twice: all skipped high digits are zero.
        for index in 1..count {
            let (word, next_borrow) = subtract_word(self.word(index), rhs.word(index), borrow);
            borrow = next_borrow;
            if word != 0 {
                let output = arena.mutable_slice(count, 0u64)?;
                output[0] = low;
                output[index] = word;
                for (next, slot) in output.iter_mut().enumerate().skip(index + 1) {
                    let (word, next_borrow) = subtract_word(self.word(next), rhs.word(next), borrow);
                    *slot = word;
                    borrow = next_borrow;
                }
                return Ok(Self::from_words(output));
            }
        }
        Ok(Self::Small(low))
    }

    pub fn mul(self, rhs: Self, arena: &mut Arena<'a>) -> Result<'a, Self> {
        let left = self.word_len();
        let right = rhs.word_len();
        if left == 0 || right == 0 {
            return Ok(Self::ZERO);
        }
        if right == 1 {
            return self.mul_word(rhs.word(0), arena);
        }
        if left == 1 {
            return rhs.mul_word(self.word(0), arena);
        }
        let count = left.checked_add(right).ok_or_else(scratch_exhausted)?;
        let words = arena.mutable_slice(count, 0u64)?;
        for i in 0..left {
            let factor = self.word(i) as u128;
            let mut carry = 0u128;
            for j in 0..right {
                // The maximum is (2^64-1)^2 + 2*(2^64-1) = 2^128-1.
                let product = factor * rhs.word(j) as u128 + words[i + j] as u128 + carry;
                words[i + j] = product as u64;
                carry = product >> 64;
            }
            // Earlier rows stop one position before this carry destination.
            words[i + right] = carry as u64;
        }
        Ok(Self::from_words(words))
    }

    pub fn shl(self, bits: u128, arena: &mut Arena<'a>) -> Result<'a, Self> {
        let previous_bits = self.bit_len();
        if previous_bits == 0 {
            return Ok(Self::ZERO);
        }
        if bits == 0 {
            return Ok(self.normalized());
        }
        let total = previous_bits.checked_add(bits).ok_or_else(scratch_exhausted)?;
        if total <= 64 {
            return Ok(Self::Small(self.word(0) << bits as u32));
        }
        let count = usize::try_from(1 + (total - 1) / 64)
            .map_err(|_| scratch_exhausted())?;
        let whole = usize::try_from(bits / 64).map_err(|_| scratch_exhausted())?;
        let partial = (bits % 64) as u32;
        let words = arena.slice_with(count, |index, _| {
            if index < whole {
                return Ok(0);
            }
            let source = index - whole;
            let mut word = self.word(source) << partial;
            if partial != 0 && source != 0 {
                word |= self.word(source - 1) >> (64 - partial);
            }
            Ok(word)
        })?;
        Ok(Self::Large(words))
    }

    pub fn shr(self, bits: u128, arena: &mut Arena<'a>) -> Result<'a, Self> {
        let previous_bits = self.bit_len();
        if bits >= previous_bits {
            return Ok(Self::ZERO);
        }
        if bits == 0 {
            return Ok(self.normalized());
        }
        // bits < bit_len bounds this conversion and every source index by the
        // physically present limb slice, even when the requested shift is u128.
        let whole = (bits / 64) as usize;
        let partial = (bits % 64) as u32;
        let shifted_word = |index: usize| {
            let source = index + whole;
            let mut word = self.word(source) >> partial;
            if partial != 0 {
                word |= self.word(source + 1) << (64 - partial);
            }
            word
        };
        let total = previous_bits - bits;
        if total <= 64 {
            return Ok(Self::Small(shifted_word(0)));
        }
        let count = (1 + (total - 1) / 64) as usize;
        Ok(Self::Large(arena.slice_with(count, |index, _| Ok(shifted_word(index)))?))
    }

    /// Divide by a nonzero machine word; a zero divisor is BadRepresentation.
    pub fn div_rem_small(self, divisor: u64, arena: &mut Arena<'a>) -> Result<'a, (Self, u64)> {
        if divisor == 0 {
            return Err(Error::new(Reason::BadRepresentation));
        }
        if divisor == 1 {
            return Ok((self.normalized(), 0));
        }
        if let Some(value) = self.to_u128() {
            return Ok((Self::from_u128(value / divisor as u128, arena)?, (value % divisor as u128) as u64));
        }
        let count = self.word_len();
        let words = arena.mutable_slice_with(count, |index, _| Ok(self.word(index)))?;
        let remainder = divide_words(words, divisor);
        Ok((Self::from_words(words), remainder))
    }

    fn normalized(self) -> Self {
        match self {
            Self::Small(_) => self,
            Self::Large(words) => Self::from_words(words),
        }
    }

    fn from_words(words: &'a [u64]) -> Self {
        let count = significant_words(words);
        if count == 0 {
            Self::ZERO
        } else if count == 1 {
            Self::Small(words[0])
        } else {
            Self::Large(&words[..count])
        }
    }

    fn mul_word(self, factor: u64, arena: &mut Arena<'a>) -> Result<'a, Self> {
        if factor == 0 {
            return Ok(Self::ZERO);
        }
        if factor == 1 {
            return Ok(self.normalized());
        }
        let count = self.word_len();
        if count <= 1 {
            return Self::from_u128(self.word(0) as u128 * factor as u128, arena);
        }
        let allocated = count.checked_add(1).ok_or_else(scratch_exhausted)?;
        let mut carry = 0u128;
        let words = arena.slice_with(allocated, |index, _| {
            let product = self.word(index) as u128 * factor as u128 + carry;
            carry = product >> 64;
            Ok(product as u64)
        })?;
        Ok(Self::from_words(words))
    }

    fn compare(self, other: Nat<'_>) -> Ordering {
        let left = self.word_len();
        let right = other.word_len();
        match left.cmp(&right) {
            Ordering::Equal => {
                for index in (0..left).rev() {
                    match self.word(index).cmp(&other.word(index)) {
                        Ordering::Equal => {}
                        order => return order,
                    }
                }
                Ordering::Equal
            }
            order => order,
        }
    }
}

impl<'a, 'b> PartialEq<Nat<'b>> for Nat<'a> {
    fn eq(&self, other: &Nat<'b>) -> bool {
        self.compare(*other) == Ordering::Equal
    }
}

impl Eq for Nat<'_> {}

impl<'a, 'b> PartialOrd<Nat<'b>> for Nat<'a> {
    fn partial_cmp(&self, other: &Nat<'b>) -> Option<Ordering> {
        Some(self.compare(*other))
    }
}

impl Ord for Nat<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.compare(*other)
    }
}

fn significant_words(words: &[u64]) -> usize {
    let mut count = words.len();
    while count != 0 && words[count - 1] == 0 {
        count -= 1;
    }
    count
}

fn subtract_word(left: u64, right: u64, borrow: bool) -> (u64, bool) {
    let (difference, first) = left.overflowing_sub(right);
    let (difference, second) = difference.overflowing_sub(borrow as u64);
    (difference, first || second)
}

/// In-place long division. The caller establishes divisor != 0.
fn divide_words(words: &mut [u64], divisor: u64) -> u64 {
    let mut remainder = 0u128;
    for word in words.iter_mut().rev() {
        let current = (remainder << 64) | *word as u128;
        *word = (current / divisor as u128) as u64;
        remainder = current % divisor as u128;
    }
    remainder as u64
}

fn scratch_exhausted<'a>() -> Error<'a> {
    Error::new(Reason::ScratchExhausted)
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::MaybeUninit;

    #[test]
    fn numeric_comparisons_and_digits_ignore_leading_zeros() {
        let words = [0x8877_6655_4433_2211, 1, 0, 0];
        let value = Nat::Large(&words);
        assert_eq!(value, Nat::Large(&words[..2]));
        assert_eq!(Nat::Large(&[0, 0]), Nat::ZERO);
        assert_eq!(Nat::Large(&[7, 0]), Nat::Small(7));
        assert_eq!(value.word_len(), 2);
        assert_eq!(value.bit_len(), 65);
        assert_eq!(value.to_u64(), None);
        assert_eq!(value.to_u128(), Some(0x1_8877_6655_4433_2211));
        assert_eq!(value.byte_le(0), 0x11);
        assert_eq!(value.byte_le(7), 0x88);
        assert_eq!(value.byte_le(8), 1);
        assert_eq!(value.byte_le(usize::MAX), 0);
        assert!(value.bit(64));
        assert!(!value.bit(65));
        assert!(!value.bit(u128::MAX));
        assert_eq!(value.cmp_u128(u64::MAX as u128), Ordering::Greater);
        assert_eq!(value.cmp_u128(u128::MAX), Ordering::Less);
        assert!(Nat::Large(&[0, 0, 8, 0]).is_power_of_two());
        assert!(!value.is_power_of_two());
        assert!(!Nat::ZERO.is_power_of_two());
    }

    #[test]
    fn carries_borrows_and_saturating_subtraction() {
        let mut storage = [MaybeUninit::uninit(); 1024];
        let mut arena = Arena::new(&mut storage);
        let maximum = Nat::Large(&[u64::MAX, u64::MAX, u64::MAX]);
        let next = maximum.add(Nat::ONE, &mut arena).unwrap();
        assert_eq!(next, Nat::Large(&[0, 0, 0, 1]));
        assert_eq!(next.sub(Nat::ONE, &mut arena).unwrap(), maximum);
        assert_eq!(maximum.sub(next, &mut arena).unwrap(), Nat::ZERO);
        assert_eq!(maximum.sub(maximum, &mut arena).unwrap(), Nat::ZERO);
        let before = arena.used();
        assert_eq!(next.sub(maximum, &mut arena).unwrap(), Nat::ONE);
        assert_eq!(arena.used(), before);
        assert_eq!(Nat::Small(u64::MAX).add(Nat::ONE, &mut arena).unwrap(), Nat::Large(&[0, 1]));
    }

    #[test]
    fn multiplication_and_division_preserve_all_carries() {
        let mut storage = [MaybeUninit::uninit(); 2048];
        let mut arena = Arena::new(&mut storage);
        let maximum = Nat::Large(&[u64::MAX, u64::MAX]);
        let square = maximum.mul(maximum, &mut arena).unwrap();
        assert_eq!(square, Nat::Large(&[1, 0, u64::MAX - 1, u64::MAX]));
        let by_word = maximum.mul(Nat::Small(u64::MAX), &mut arena).unwrap();
        assert_eq!(by_word, Nat::Large(&[1, u64::MAX, u64::MAX - 1]));
        let (quotient, remainder) = by_word.div_rem_small(u64::MAX, &mut arena).unwrap();
        assert_eq!(quotient, maximum);
        assert_eq!(remainder, 0);
        let with_remainder = by_word.add(Nat::Small(37), &mut arena).unwrap();
        let (quotient, remainder) = with_remainder.div_rem_small(u64::MAX, &mut arena).unwrap();
        assert_eq!(quotient, maximum);
        assert_eq!(remainder, 37);
        assert_eq!(Nat::ZERO.div_rem_small(0, &mut arena).unwrap_err().reason, Reason::BadRepresentation);
    }

    #[test]
    fn shifts_cross_limb_boundaries_and_handle_huge_counts() {
        let mut storage = [MaybeUninit::uninit(); 4096];
        let mut arena = Arena::new(&mut storage);
        let value = Nat::Large(&[0x8000_0000_0000_0001, 3]);
        assert_eq!(value.shl(1, &mut arena).unwrap(), Nat::Large(&[2, 7]));
        assert_eq!(value.shl(64, &mut arena).unwrap(), Nat::Large(&[0, 0x8000_0000_0000_0001, 3]));
        assert_eq!(value.shr(1, &mut arena).unwrap(), Nat::Large(&[0xc000_0000_0000_0000, 1]));
        assert_eq!(value.shr(64, &mut arena).unwrap(), Nat::Small(3));
        for shift in [0, 1, 63, 64, 65, 127, 128, 129] {
            let shifted = value.shl(shift, &mut arena).unwrap();
            assert_eq!(shifted.shr(shift, &mut arena).unwrap(), value);
        }
        assert_eq!(value.shr(u128::MAX, &mut arena).unwrap(), Nat::ZERO);
        assert_eq!(Nat::ZERO.shl(u128::MAX, &mut arena).unwrap(), Nat::ZERO);
        assert_eq!(value.shl(u128::MAX, &mut arena).unwrap_err().reason, Reason::ScratchExhausted);
        assert_eq!(Nat::ONE.shl((usize::MAX as u128) * 64, &mut arena).unwrap_err().reason, Reason::ScratchExhausted);
    }

    #[test]
    fn decimal_above_256_bits_and_little_endian_round_trip() {
        let mut storage = [MaybeUninit::uninit(); 4096];
        let mut arena = Arena::new(&mut storage);
        // 2^300 + 123: larger than any fixed SSZ uint width, but valid metadata.
        let text = "2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397499";
        let value = Nat::from_decimal(text, &mut arena).unwrap();
        assert_eq!(value, Nat::Large(&[123, 0, 0, 0, 1 << 44]));
        assert_eq!(value.bit_len(), 301);
        assert_eq!(value.decimal(&mut arena).unwrap(), text);
        let bytes = arena.bytes_with(40, |index| value.byte_le(index)).unwrap();
        assert_eq!(Nat::from_le_bytes(bytes, &mut arena).unwrap(), value);
        assert_eq!(Nat::from_decimal("00018446744073709551615", &mut arena).unwrap(), Nat::Small(u64::MAX));
        let word_boundary = Nat::from_decimal("00018446744073709551616", &mut arena).unwrap();
        assert_eq!(word_boundary, Nat::Large(&[0, 1]));
        assert_eq!(word_boundary.decimal(&mut arena).unwrap(), "18446744073709551616");
        assert_eq!(Nat::from_decimal("00000", &mut arena).unwrap().decimal(&mut arena).unwrap(), "0");
        assert_eq!(Nat::from_le_bytes(&[1, 0, 0, 0, 0, 0, 0, 0, 0], &mut arena).unwrap(), Nat::ONE);
    }

    #[test]
    fn malformed_decimal_precedes_scratch_and_small_values_need_none() {
        let mut storage = [];
        let mut arena = Arena::new(&mut storage);
        for text in ["", "-1", "+1", " 1", "1 ", "1_000", "١", "184467440737095516160x"] {
            assert_eq!(Nat::from_decimal(text, &mut arena).unwrap_err().reason, Reason::BadRepresentation);
        }
        assert_eq!(Nat::from_decimal("18446744073709551615", &mut arena).unwrap(), Nat::Small(u64::MAX));
        assert_eq!(Nat::from_decimal("18446744073709551616", &mut arena).unwrap_err().reason, Reason::ScratchExhausted);
        assert_eq!(Nat::Small(7).mul(Nat::Small(9), &mut arena).unwrap(), Nat::Small(63));
        assert_eq!(Nat::Large(&[0, 1]).sub(Nat::ONE, &mut arena).unwrap(), Nat::Small(u64::MAX));
        assert_eq!(Nat::Large(&[0, 1]).shr(1, &mut arena).unwrap(), Nat::Small(1 << 63));
        assert_eq!(arena.used(), 0);
    }
}
