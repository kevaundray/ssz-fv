#![no_std]

/// Write the SSZ little-endian encoding of a uint64 into caller-owned memory.
///
/// # Safety
/// `output` must point to eight writable bytes. No alignment is required.
#[no_mangle]
pub unsafe extern "C" fn ssz_store_u64(output: *mut u8, value: u64) {
    core::ptr::write_unaligned(output.cast::<u64>(), value.to_le());
}

/// Read an SSZ uint64 from an exactly eight-byte input scope.
///
/// # Safety
/// `input` must point to eight readable bytes. No alignment is required.
/// The caller is responsible for checking the SSZ input scope length.
#[no_mangle]
pub unsafe extern "C" fn ssz_load_u64(input: *const u8) -> u64 {
    u64::from_le(core::ptr::read_unaligned(input.cast::<u64>()))
}
