use core::marker::PhantomData;
use core::mem::{align_of, size_of, MaybeUninit};
use core::ptr::{self, NonNull};
use core::slice;

use crate::{Error, Reason, Result};

/// A monotonically allocated view of caller-owned storage.
///
/// Returned references borrow the original storage, not the temporary borrow of
/// the arena. There is deliberately no reset: live allocations are never reused.
/// Alignment padding and allocations abandoned by an error remain consumed.
///
/// The backing bytes must be MaybeUninit: writing a valid Copy value can leave
/// its padding uninitialized, even if the storage originally contained zeros.
/// After typed borrows expire, callers may reuse storage but must not assume
/// those padding bytes are initialized.
pub struct Arena<'a> {
    base: NonNull<u8>,
    capacity: usize,
    used: usize,
    storage: PhantomData<&'a mut [MaybeUninit<u8>]>,
}

impl<'a> Arena<'a> {
    pub fn new(storage: &'a mut [MaybeUninit<u8>]) -> Self {
        // Slice pointers are non-null, including for an empty slice.
        let base = NonNull::new(storage.as_mut_ptr().cast::<u8>()).unwrap();
        Self { base, capacity: storage.len(), used: 0, storage: PhantomData }
    }

    pub fn used(&self) -> usize {
        self.used
    }

    /// Reserve disjoint, aligned storage, without exposing uninitialized values.
    fn reserve<T>(&mut self, len: usize) -> Result<'a, NonNull<T>> {
        if len == 0 || size_of::<T>() == 0 {
            // A dangling pointer is aligned and non-null for T. No backing bytes
            // are needed for an empty allocation or for zero-sized elements.
            return Ok(NonNull::dangling());
        }
        let exhausted = || Error::new(Reason::ScratchExhausted);
        let bytes = len.checked_mul(size_of::<T>()).ok_or_else(exhausted)?;
        if bytes > isize::MAX as usize {
            return Err(exhausted());
        }
        let address = (self.base.as_ptr() as usize)
            .checked_add(self.used).ok_or_else(exhausted)?;
        let mask = align_of::<T>() - 1;
        let aligned = address.checked_add(mask).ok_or_else(exhausted)? & !mask;
        let start = self.used.checked_add(aligned - address).ok_or_else(exhausted)?;
        let end = start.checked_add(bytes).ok_or_else(exhausted)?;
        if end > self.capacity {
            return Err(exhausted());
        }
        // Reserve before any initializer runs, so nested allocations cannot
        // overlap these bytes. The backing storage bounds every pointer offset and
        // has at most isize::MAX bytes; start..end is inside that allocation.
        self.used = end;
        // SAFETY: start is in bounds, alignment was checked arithmetically, and
        // casting retains the original allocation's pointer provenance.
        Ok(unsafe { NonNull::new_unchecked(self.base.as_ptr().add(start).cast::<T>()) })
    }

    pub fn slice_with<T: Copy + 'a, F>(&mut self, len: usize, fill: F) -> Result<'a, &'a [T]>
    where
        F: FnMut(usize, &mut Arena<'a>) -> Result<'a, T>,
    {
        Ok(self.mutable_slice_with(len, fill)?)
    }

    /// Initialize a mutable slice once; the initializer may allocate nested data.
    pub fn mutable_slice_with<T: Copy + 'a, F>(&mut self, len: usize, mut fill: F) -> Result<'a, &'a mut [T]>
    where
        F: FnMut(usize, &mut Arena<'a>) -> Result<'a, T>,
    {
        let allocation = self.reserve::<T>(len)?;
        for index in 0..len {
            let value = fill(index, self)?;
            // SAFETY: reserve provides aligned storage for len elements, and
            // each element is written exactly once. For a ZST the aligned
            // dangling pointer requires no backing bytes. Nested allocations
            // cannot overlap this reserved region.
            unsafe { allocation.as_ptr().add(index).write(value) };
        }
        // SAFETY: every element is initialized and the byte length is bounded
        // by isize::MAX. No alias of this region has been exposed. The arena
        // exclusively owns the backing storage for 'a; its increasing cursor
        // prevents overlapping allocations, and its PhantomData retains the
        // caller's exclusive storage borrow even when this Arena borrow ends.
        Ok(unsafe { slice::from_raw_parts_mut(allocation.as_ptr(), len) })
    }

    pub fn copy<T: Copy + 'a>(&mut self, input: &[T]) -> Result<'a, &'a [T]> {
        let allocation = self.reserve::<T>(input.len())?;
        // SAFETY: the new aligned region is disjoint from all existing arena
        // allocations, including input if it came from this arena. Otherwise
        // input cannot alias the exclusively borrowed backing bytes in safe
        // code. Copy initializes every element, including the zero-byte cases.
        unsafe { ptr::copy_nonoverlapping(input.as_ptr(), allocation.as_ptr(), input.len()) };
        // SAFETY: the initialized region remains exclusively reserved for 'a,
        // with the same size/alignment/lifetime invariants as slice_with.
        Ok(unsafe { slice::from_raw_parts(allocation.as_ptr(), input.len()) })
    }

    pub fn one<T: Copy + 'a>(&mut self, value: T) -> Result<'a, &'a T> {
        Ok(&self.slice_with(1, |_, _| Ok(value))?[0])
    }

    pub fn bytes_with<F>(&mut self, len: usize, mut fill: F) -> Result<'a, &'a [u8]>
    where
        F: FnMut(usize) -> u8,
    {
        self.slice_with(len, |index, _| Ok(fill(index)))
    }

    pub fn utf8(&mut self, input: &str) -> Result<'a, &'a str> {
        let bytes = self.copy(input.as_bytes())?;
        // SAFETY: copying bytes from a str preserves their valid UTF-8.
        Ok(unsafe { core::str::from_utf8_unchecked(bytes) })
    }

    /// Return initialized mutable storage, disjoint from all other allocations.
    pub fn mutable_slice<T: Copy + 'a>(&mut self, len: usize, initial: T) -> Result<'a, &'a mut [T]> {
        self.mutable_slice_with(len, |_, _| Ok(initial))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy)]
    #[repr(align(64))]
    struct Aligned(u64);

    #[test]
    fn aligned_and_nested_allocations_are_disjoint() {
        let mut storage = [MaybeUninit::uninit(); 512];
        let mut arena = Arena::new(&mut storage[1..]);
        let first = arena.mutable_slice(3, 7u8).unwrap();
        let aligned = arena.one(Aligned(91)).unwrap();
        let nested = arena.slice_with(3, |index, arena| arena.one(index as u64 + 10)).unwrap();
        let last = arena.mutable_slice(3, 8u8).unwrap();
        first[1] = 42;
        last[1] = 43;
        assert_eq!((aligned as *const Aligned as usize) % 64, 0);
        assert_eq!(aligned.0, 91);
        assert_eq!(nested.iter().map(|value| **value).sum::<u64>(), 33);
        assert_eq!(first, &[7, 42, 7]);
        assert_eq!(last, &[8, 43, 8]);
    }

    #[test]
    fn exact_capacity_and_overflow_fail_without_reusing_storage() {
        let mut storage = [MaybeUninit::uninit(); 3];
        let mut arena = Arena::new(&mut storage);
        let bytes = arena.copy(&[1u8, 2, 3]).unwrap();
        assert_eq!(arena.used(), 3);
        assert_eq!(arena.one(4u8).unwrap_err().reason, Reason::ScratchExhausted);
        assert_eq!(arena.mutable_slice(usize::MAX, 0u64).unwrap_err().reason, Reason::ScratchExhausted);
        assert_eq!(arena.mutable_slice(isize::MAX as usize + 1, 0u8).unwrap_err().reason, Reason::ScratchExhausted);
        assert_eq!(bytes, &[1, 2, 3]);
        assert_eq!(arena.used(), 3);
    }

    #[test]
    fn empty_and_zero_sized_allocations_need_no_storage() {
        let mut storage = [];
        let mut arena = Arena::new(&mut storage);
        assert_eq!(arena.mutable_slice(4, ()).unwrap(), &[(); 4]);
        assert!(arena.slice_with::<u64, _>(0, |_, _| unreachable!()).unwrap().is_empty());
        assert_eq!(arena.utf8("").unwrap(), "");
        assert_eq!(arena.used(), 0);
        assert_eq!(arena.one(0u8).unwrap_err().reason, Reason::ScratchExhausted);
    }

    #[test]
    fn failed_initializer_does_not_expose_or_reuse_partial_values() {
        let mut storage = [MaybeUninit::uninit(); 16];
        let mut arena = Arena::new(&mut storage);
        let result = arena.slice_with(4, |index, arena| {
            if index == 1 {
                arena.one(99u8)?;
                Err(Error::new(Reason::BadRepresentation))
            } else {
                Ok(index as u8)
            }
        });
        assert_eq!(result.unwrap_err().reason, Reason::BadRepresentation);
        assert_eq!(arena.used(), 5);
        assert_eq!(arena.copy(&[10u8; 11]).unwrap(), &[10; 11]);
        assert_eq!(arena.one(0u8).unwrap_err().reason, Reason::ScratchExhausted);
    }
}
