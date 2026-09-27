#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

//! Caller-owned C interface to the native SSZ implementation.
//!
//! # Safety contract for every exported function
//!
//! Pointer checks reject null nonempty spans, misalignment, overflowing sizes,
//! and wrapping addresses. They cannot establish allocation provenance, actual
//! allocation bounds, initialization, lifetime, or absence of aliasing: these
//! remain the C caller's obligations, including for recursively reached inputs.
//! Each nonempty span must belong to one live allocation. Input spans contain
//! initialized values and remain immutable; required output slots are writable
//! and aligned, but need not initially contain values. Serialization output
//! bytes may likewise be uninitialized: serialization never reads them.
//! Empty spans may have null data. JSON graphs are finite and acyclic, every
//! struct field is initialized, and inactive fields are ignored. JSON strings,
//! object names, and numeric tokens must be UTF-8; numbers are parsed JSON
//! numeric tokens rather than floating-point approximations.
//!
//! Schema and value pointers must be original, live handles returned by this
//! library, not fabricated objects or handles of another kind. Handle storage
//! and all recursively borrowed inputs must remain alive and immutable while
//! any derived handle, JSON view, natural-number limbs, proof, or error payload
//! is in use. In particular, decoding can borrow the encoded input, schema
//! parsing can borrow JSON names, and errors can borrow input names or limbs.
//! Returning from a call does not end these input-lifetime obligations.
//!
//! The scratch descriptor is initialized, writable, and disjoint from its
//! backing allocation. Only `[used, capacity)` is borrowed mutably by a call;
//! earlier allocations may be passed back as immutable handles or views.
//! The suffix is disjoint from every input, output, and parameter object. All
//! mutable output spans (including error and scratch descriptors) are mutually
//! disjoint and do not overlap inputs. Immutable input spans may share storage.
//! Scratch may contain uninitialized bytes, including padding of past typed
//! allocations. Never reset, mutate, relocate, or reuse referenced storage until
//! all handles, views, and error payloads depending on it have expired.
//!
//! Failures preserve ordinary output slots. Serialization may change bytes
//! inside its output capacity on failure. Scratch consumption is retained on
//! both success and failure. The optional error slot is cleared on success and
//! otherwise receives the exact native reason and natural/text payloads.
//! This ABI and native compilation do not constitute an ISA-equivalence proof.

use core::mem::{align_of, size_of, MaybeUninit};
use core::{ptr, slice, str};
use ssz_fv_native::{
    codec, descriptor, hash, indices, json, layout, merkle, proof, schema, verify,
    Arena, Desc, Error, Json, Nat, Reason, Result, Spelling, Value,
};

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
compile_error!("the native C ABI supports x86-64 and AArch64 only");

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    // SAFETY: these unconditional trapping instructions have no operands or
    // memory accesses and cannot return. No runtime or allocator is required.
    #[cfg(target_arch = "x86_64")]
    unsafe { core::arch::asm!("ud2", options(noreturn, nomem, nostack)) }
    // SAFETY: BRK raises a synchronous exception instead of continuing after a
    // violated invariant. It has no operands or memory accesses and cannot return.
    #[cfg(target_arch = "aarch64")]
    unsafe { core::arch::asm!("brk #0", options(noreturn, nomem, nostack)) }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct SszBytes {
    pub data: *const u8,
    pub len: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct SszNat {
    pub small: u64,
    pub limbs: *const u64,
    pub limb_count: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct SszScratch {
    pub data: *mut u8,
    pub capacity: usize,
    pub used: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct SszError {
    pub reason: u32,
    pub args: [SszNat; 3],
    pub text: SszBytes,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct SszJson {
    pub tag: u32,
    pub boolean: u32,
    pub text: SszBytes,
    pub items: *const SszJson,
    pub item_count: usize,
    pub fields: *const SszJsonField,
    pub field_count: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct SszJsonField {
    pub name: SszBytes,
    pub value: SszJson,
}

/// Opaque marker; actual storage is a private `Schema`, never this marker.
#[repr(C)]
pub struct SszSchema {
    _private: [u8; 0],
}

/// Opaque marker; actual storage is a native `Value`, never this marker.
#[repr(C)]
pub struct SszValue {
    _private: [u8; 0],
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct SszHashes {
    pub data: *const u8,
    pub count: usize,
}

#[derive(Clone, Copy)]
struct Schema<'a> {
    desc: Desc<'a>,
    spelling: Spelling<'a>,
}

const EMPTY_BYTES: SszBytes = SszBytes { data: ptr::null(), len: 0 };
const ZERO_NAT: SszNat = SszNat { small: 0, limbs: ptr::null(), limb_count: 0 };
const NO_ERROR: SszError = SszError { reason: 0, args: [ZERO_NAT; 3], text: EMPTY_BYTES };

fn bad_representation<'a>() -> Error<'a> {
    Error::new(Reason::BadRepresentation)
}

/// Checks only arithmetic/alignment, not provenance or allocation validity.
fn check_span<'a, T>(data: *const T, len: usize) -> Result<'a, ()> {
    if len == 0 {
        return Ok(());
    }
    let bytes = len.checked_mul(size_of::<T>()).ok_or_else(bad_representation)?;
    if data.is_null()
        || data.addr() % align_of::<T>() != 0
        || bytes > isize::MAX as usize
        || data.addr().checked_add(bytes).is_none()
    {
        return Err(bad_representation());
    }
    Ok(())
}

/// Caller guarantees readable, initialized T values, a single allocation, and
/// an immutable borrow lasting 'a. Numeric checks alone cannot establish this.
unsafe fn input_slice<'a, T>(data: *const T, len: usize) -> Result<'a, &'a [T]> {
    check_span(data, len)?;
    if len == 0 {
        return Ok(&[]);
    }
    // SAFETY: check_span establishes nonnull/alignment/size/address bounds;
    // the caller establishes allocation provenance, initialization, and the
    // immutable lifetime 'a. The original pointer retains its provenance.
    Ok(unsafe { slice::from_raw_parts(data, len) })
}

unsafe fn input_ref<'a, T>(data: *const T) -> Result<'a, &'a T> {
    // SAFETY: caller supplies one initialized, live T under input_slice's
    // immutable lifetime/allocation obligations; the helper checks arithmetic.
    Ok(&unsafe { input_slice(data, 1)? }[0])
}

unsafe fn input_bytes<'a>(bytes: SszBytes) -> Result<'a, &'a [u8]> {
    // SAFETY: the recursively applicable input contract covers this byte span.
    unsafe { input_slice(bytes.data, bytes.len) }
}

unsafe fn input_text<'a>(bytes: SszBytes) -> Result<'a, &'a str> {
    // SAFETY: byte validity and immutable lifetime come from the input contract;
    // UTF-8 is checked before constructing a str.
    str::from_utf8(unsafe { input_bytes(bytes)? }).map_err(|_| bad_representation())
}

unsafe fn input_nat<'a>(number: SszNat) -> Result<'a, Nat<'a>> {
    if number.limb_count == 0 {
        Ok(Nat::Small(number.small))
    } else {
        // SAFETY: the caller retains the aligned initialized limb allocation
        // for all uses of the returned Nat; input_slice checks span arithmetic.
        Ok(Nat::Large(unsafe { input_slice(number.limbs, number.limb_count)? }))
    }
}

unsafe fn input_schema<'a>(handle: *const SszSchema) -> Result<'a, &'a Schema<'a>> {
    // SAFETY: only a live handle returned by ssz_schema_from_json is admitted.
    // Its allocation contains exactly Schema, not the opaque marker; casting
    // retains provenance, and input_ref checks Schema's actual size/alignment.
    unsafe { input_ref(handle.cast::<Schema<'a>>()) }
}

unsafe fn input_value<'a>(handle: *const SszValue) -> Result<'a, &'a Value<'a>> {
    // SAFETY: the caller supplies a live value handle allocated by this crate.
    // Actual Value layout/alignment is checked, and all nested borrows stay live.
    unsafe { input_ref(handle.cast::<Value<'a>>()) }
}

fn output_bytes(bytes: &[u8]) -> SszBytes {
    SszBytes { data: if bytes.is_empty() { ptr::null() } else { bytes.as_ptr() }, len: bytes.len() }
}

fn output_nat(number: Nat<'_>) -> SszNat {
    match number {
        Nat::Small(small) => SszNat { small, ..ZERO_NAT },
        Nat::Large(limbs) => SszNat {
            small: 0,
            limbs: if limbs.is_empty() { ptr::null() } else { limbs.as_ptr() },
            limb_count: limbs.len(),
        },
    }
}

fn output_error(error: Error<'_>) -> SszError {
    SszError {
        reason: error.reason as u32,
        args: error.args.map(output_nat),
        text: output_bytes(error.text.as_bytes()),
    }
}

fn output_hashes(hashes: &[hash::Hash]) -> SszHashes {
    // [u8; 32] has alignment one and no padding; consecutive elements therefore
    // have exactly the C ABI's 32-byte stride. The scratch allocation stays live.
    SszHashes {
        data: if hashes.is_empty() { ptr::null() } else { hashes.as_ptr().cast() },
        count: hashes.len(),
    }
}

fn hold_value<'a>(value: Value<'a>, arena: &mut Arena<'a>) -> Result<'a, *const SszValue> {
    Ok((arena.one(value)? as *const Value<'a>).cast())
}

/// Commit a complete result only after success. T is a foreign-layout value,
/// opaque pointer, byte array, or scalar; output/error spans are disjoint.
unsafe fn dispatch<'a, T>(
    out: *mut T,
    error: *mut SszError,
    operation: impl FnOnce() -> Result<'a, T>,
) -> u32 {
    if !error.is_null() && check_span(error, 1).is_err() {
        return Reason::BadRepresentation as u32;
    }
    let result = check_span(out, 1).and_then(|()| operation());
    match result {
        Ok(value) => {
            // SAFETY: span checks establish size/alignment, and the C caller
            // guarantees writable output storage disjoint from all input/error
            // borrows. ptr::write does not read or drop an uninitialized slot.
            unsafe { out.write(value) };
            if !error.is_null() {
                // SAFETY: checked above; caller supplies writable disjoint
                // storage and no still-live immutable borrow of the error slot.
                unsafe { error.write(NO_ERROR) };
            }
            0
        }
        Err(failure) => {
            if !error.is_null() {
                // SAFETY: checked above and caller-owned writable/disjoint;
                // referenced payloads live in retained input or scratch storage.
                unsafe { error.write(output_error(failure)) };
            }
            failure.reason as u32
        }
    }
}

unsafe fn scratch_call<'a, T>(
    scratch: *mut SszScratch,
    out: *mut T,
    error: *mut SszError,
    operation: impl FnOnce(&mut Arena<'a>) -> Result<'a, T>,
) -> u32 {
    // SAFETY: this function inherits dispatch's output and error contract.
    unsafe {
        dispatch(out, error, || {
            check_span(scratch, 1)?;
            // The scratch descriptor is initialized and readable/writable by
            // contract. Reading it by value avoids borrowing the entire backing
            // allocation or keeping a descriptor reference alive across writes.
            let state = scratch.read();
            if state.used > state.capacity {
                return Err(bad_representation());
            }
            check_span(state.data, state.capacity)?;
            let remaining = state.capacity - state.used;
            let storage: &'a mut [MaybeUninit<u8>] = if remaining == 0 {
                &mut []
            } else {
                // The checked total span belongs to one caller allocation.
                // used < capacity, so add stays within that allocation and
                // retains provenance. The suffix alone is exclusively borrowed;
                // past handles remain valid outside it. MaybeUninit permits
                // arbitrary padding and never reads the raw scratch contents.
                slice::from_raw_parts_mut(state.data.add(state.used).cast(), remaining)
            };
            let mut arena = Arena::new(storage);
            let result = operation(&mut arena);
            // arena.used() <= remaining, so addition cannot exceed capacity.
            // Descriptor storage is writable and disjoint from its backing
            // allocation, all inputs, and outputs. Only the cursor is changed.
            ptr::addr_of_mut!((*scratch).used).write(state.used + arena.used());
            result
        })
    }
}

unsafe fn import_json<'a>(document: &SszJson, arena: &mut Arena<'a>) -> Result<'a, Json<'a>> {
    // SAFETY: the C input contract applies recursively to every active field,
    // including finite acyclic arrays/objects and immutable referenced storage.
    // Each conversion helper checks actual element size/alignment before reads.
    unsafe {
        match document.tag {
            0 => Ok(Json::Null),
            1 => match document.boolean {
                0 => Ok(Json::Bool(false)),
                1 => Ok(Json::Bool(true)),
                _ => Err(bad_representation()),
            },
            2 => Ok(Json::Number(input_text(document.text)?)),
            3 => Ok(Json::String(input_text(document.text)?)),
            4 => {
                let items = input_slice(document.items, document.item_count)?;
                Ok(Json::Array(arena.slice_with(items.len(), |index, arena| {
                    import_json(&items[index], arena)
                })?))
            }
            5 => {
                let fields = input_slice(document.fields, document.field_count)?;
                Ok(Json::Object(arena.slice_with(fields.len(), |index, arena| {
                    let field = &fields[index];
                    Ok((input_text(field.name)?, import_json(&field.value, arena)?))
                })?))
            }
            _ => Err(bad_representation()),
        }
    }
}

fn export_json<'a>(document: &Json<'a>, arena: &mut Arena<'a>) -> Result<'a, SszJson> {
    let mut result = SszJson {
        tag: 0,
        boolean: 0,
        text: EMPTY_BYTES,
        items: ptr::null(),
        item_count: 0,
        fields: ptr::null(),
        field_count: 0,
    };
    match document {
        Json::Null => (),
        Json::Bool(value) => {
            result.tag = 1;
            result.boolean = u32::from(*value);
        }
        Json::Number(text) => {
            result.tag = 2;
            result.text = output_bytes(text.as_bytes());
        }
        Json::String(text) => {
            result.tag = 3;
            result.text = output_bytes(text.as_bytes());
        }
        Json::Array(items) => {
            result.tag = 4;
            let items = arena.slice_with(items.len(), |index, arena| export_json(&items[index], arena))?;
            result.items = if items.is_empty() { ptr::null() } else { items.as_ptr() };
            result.item_count = items.len();
        }
        Json::Object(fields) => {
            result.tag = 5;
            let fields = arena.slice_with(fields.len(), |index, arena| {
                Ok(SszJsonField {
                    name: output_bytes(fields[index].0.as_bytes()),
                    value: export_json(&fields[index].1, arena)?,
                })
            })?;
            result.fields = if fields.is_empty() { ptr::null() } else { fields.as_ptr() };
            result.field_count = fields.len();
        }
    }
    Ok(result)
}

unsafe fn input_nats<'a>(
    data: *const SszNat,
    count: usize,
    arena: &mut Arena<'a>,
) -> Result<'a, &'a [Nat<'a>]> {
    // SAFETY: the caller supplies initialized foreign Nat records and retains
    // each borrowed limb span. Only native slice metadata is allocated here.
    unsafe {
        let numbers = input_slice(data, count)?;
        arena.slice_with(count, |index, _| input_nat(numbers[index]))
    }
}

unsafe fn input_nodes<'a>(
    data: *const SszBytes,
    count: usize,
    arena: &mut Arena<'a>,
) -> Result<'a, &'a [&'a [u8]]> {
    // SAFETY: initialized records and their immutable spans obey the recursive
    // input contract. Node contents are borrowed, never copied or width-clamped.
    unsafe {
        let nodes = input_slice(data, count)?;
        arena.slice_with(count, |index, _| input_bytes(nodes[index]))
    }
}

/// Parse and validate a schema, retaining its original byte-alias spelling.
/// # Safety
/// The module-wide C pointer, lifetime, disjointness, and scratch contract applies.
#[no_mangle]
pub unsafe extern "C" fn ssz_schema_from_json(
    document: *const SszJson,
    scratch: *mut SszScratch,
    out: *mut *const SszSchema,
    error: *mut SszError,
) -> u32 {
    // SAFETY: the exported function's contract supplies recursively initialized
    // JSON and disjoint scratch/output storage; helpers check span arithmetic.
    unsafe {
        scratch_call(scratch, out, error, |arena| {
            let document = import_json(input_ref(document)?, arena)?;
            let (desc, spelling) = descriptor::read_descriptor(&document, arena)?;
            schema::validate(&desc, arena)?;
            Ok((arena.one(Schema { desc, spelling })? as *const Schema<'_>).cast())
        })
    }
}

/// Read SSZ JSON into an opaque value; input-derived borrows can outlive this call.
/// # Safety
/// The module-wide C pointer, lifetime, disjointness, and scratch contract applies.
#[no_mangle]
pub unsafe extern "C" fn ssz_value_from_json(
    schema: *const SszSchema,
    document: *const SszJson,
    scratch: *mut SszScratch,
    out: *mut *const SszValue,
    error: *mut SszError,
) -> u32 {
    // SAFETY: live original schema handle, recursive JSON input, and retained
    // immutable borrows are supplied by the caller; helpers validate spans.
    unsafe {
        scratch_call(scratch, out, error, |arena| {
            let schema = input_schema(schema)?;
            let document = import_json(input_ref(document)?, arena)?;
            let value = json::value_of(&schema.desc, schema.spelling, &document, arena)?;
            hold_value(value, arena)
        })
    }
}

/// Return a scratch-resident JSON tree whose text may also borrow handle inputs.
/// # Safety
/// The module-wide C pointer, lifetime, disjointness, and scratch contract applies.
#[no_mangle]
pub unsafe extern "C" fn ssz_value_to_json(
    schema: *const SszSchema,
    value: *const SszValue,
    scratch: *mut SszScratch,
    out: *mut *const SszJson,
    error: *mut SszError,
) -> u32 {
    // SAFETY: the caller provides original live handles and disjoint writable
    // scratch/output spans; all nested borrows remain immutable and live.
    unsafe {
        scratch_call(scratch, out, error, |arena| {
            let schema = input_schema(schema)?;
            let document = json::json_of(&schema.desc, schema.spelling, input_value(value)?, arena)?;
            let document = export_json(&document, arena)?;
            Ok(arena.one(document)? as *const SszJson)
        })
    }
}

/// Construct the schema's default, preserving NoDefault for compatible unions.
/// # Safety
/// The module-wide C pointer, lifetime, disjointness, and scratch contract applies.
#[no_mangle]
pub unsafe extern "C" fn ssz_default_value(
    schema: *const SszSchema,
    scratch: *mut SszScratch,
    out: *mut *const SszValue,
    error: *mut SszError,
) -> u32 {
    // SAFETY: original handle and disjoint writable outputs/suffix are caller
    // obligations; actual typed handle layout is checked by input_schema.
    unsafe {
        scratch_call(scratch, out, error, |arena| {
            let value = schema::default_value(&input_schema(schema)?.desc, arena)?;
            hold_value(value, arena)
        })
    }
}

/// Compare a value with its schema's default.
/// # Safety
/// The module-wide C pointer, lifetime, disjointness, and scratch contract applies.
#[no_mangle]
pub unsafe extern "C" fn ssz_is_zero(
    schema: *const SszSchema,
    value: *const SszValue,
    scratch: *mut SszScratch,
    out: *mut u8,
    error: *mut SszError,
) -> u32 {
    // SAFETY: both handles and recursively borrowed storage remain live outside
    // the exclusive scratch suffix; helpers check all direct pointer spans.
    unsafe {
        scratch_call(scratch, out, error, |arena| {
            Ok(u8::from(schema::is_zero(&input_schema(schema)?.desc, input_value(value)?, arena)?))
        })
    }
}

/// Compare Merkle-layout compatibility without allocating scratch storage.
/// # Safety
/// The module-wide C pointer, lifetime, and disjointness contract applies.
#[no_mangle]
pub unsafe extern "C" fn ssz_compatible(
    left: *const SszSchema,
    right: *const SszSchema,
    out: *mut u8,
    error: *mut SszError,
) -> u32 {
    // SAFETY: caller supplies live immutable handles and disjoint writable
    // outputs; input_schema/dispatch check actual sizes and alignment.
    unsafe {
        dispatch(out, error, || {
            Ok(u8::from(schema::compatible(&input_schema(left)?.desc, &input_schema(right)?.desc)))
        })
    }
}

/// Encode into writable bytes, preserving bytes after written size.
/// On failure the output buffer may change, but `written` remains unchanged.
/// # Safety
/// The module-wide C pointer, lifetime, disjointness, and scratch contract applies.
#[no_mangle]
pub unsafe extern "C" fn ssz_serialize(
    schema: *const SszSchema,
    value: *const SszValue,
    output: *mut u8,
    capacity: usize,
    scratch: *mut SszScratch,
    written: *mut usize,
    error: *mut SszError,
) -> u32 {
    // SAFETY: caller supplies exclusively writable serialization
    // bytes disjoint from handles, suffix, and result slots. Zero length uses
    // an actual empty Rust slice; nonempty spans are checked before creation.
    unsafe {
        scratch_call(scratch, written, error, |arena| {
            check_span(output, capacity)?;
            let output = if capacity == 0 { &mut [] } else { slice::from_raw_parts_mut(output.cast::<MaybeUninit<u8>>(), capacity) };
            codec::serialize(&input_schema(schema)?.desc, input_value(value)?, output, arena)
        })
    }
}

/// Decode one exact byte scope. The resulting value can borrow `input.data`.
/// # Safety
/// The module-wide contract applies; retain input bytes for the value's lifetime.
#[no_mangle]
pub unsafe extern "C" fn ssz_deserialize(
    schema: *const SszSchema,
    input: SszBytes,
    scratch: *mut SszScratch,
    out: *mut *const SszValue,
    error: *mut SszError,
) -> u32 {
    // SAFETY: the original schema and immutable input allocation outlive the
    // returned value; disjoint suffix/output storage is supplied by the caller.
    unsafe {
        scratch_call(scratch, out, error, |arena| {
            let value = codec::deserialize(&input_schema(schema)?.desc, input_bytes(input)?, arena)?;
            hold_value(value, arena)
        })
    }
}

/// Calculate the schema-aware hash-tree root.
/// # Safety
/// The module-wide contract applies; out32 points to 32 disjoint writable bytes.
#[no_mangle]
pub unsafe extern "C" fn ssz_hash_tree_root(
    schema: *const SszSchema,
    value: *const SszValue,
    scratch: *mut SszScratch,
    out32: *mut u8,
    error: *mut SszError,
) -> u32 {
    // SAFETY: casting to [u8; 32] retains provenance and alignment one while
    // making dispatch validate/write the complete output span only on success.
    unsafe {
        scratch_call(scratch, out32.cast(), error, |arena| {
            layout::hash_tree_root(&input_schema(schema)?.desc, input_value(value)?, arena)
        })
    }
}

/// Resolve an index-vector (format 0) or proof-vector (format 1) JSON path.
/// # Safety
/// The module-wide contract applies; returned limbs may borrow retained scratch.
#[no_mangle]
pub unsafe extern "C" fn ssz_generalized_index(
    schema: *const SszSchema,
    path: *const SszJson,
    proof_format: u32,
    scratch: *mut SszScratch,
    out: *mut SszNat,
    error: *mut SszError,
) -> u32 {
    // SAFETY: original schema, recursive immutable path, and writable disjoint
    // outputs/suffix obey the exported contract; each pointer span is checked.
    unsafe {
        scratch_call(scratch, out, error, |arena| {
            if proof_format > 1 { return Err(bad_representation()); }
            let schema = input_schema(schema)?;
            let path = import_json(input_ref(path)?, arena)?;
            let path = descriptor::read_path(&schema.desc, &path, proof_format == 1, arena)?;
            Ok(output_nat(indices::generalized_index(&schema.desc, path, arena)?))
        })
    }
}

/// Read a schema-aware tree node; unlike a branch request, index one is allowed.
/// # Safety
/// The module-wide contract applies; out32 points to 32 disjoint writable bytes.
#[no_mangle]
pub unsafe extern "C" fn ssz_node_root(
    schema: *const SszSchema,
    value: *const SszValue,
    index: SszNat,
    scratch: *mut SszScratch,
    out32: *mut u8,
    error: *mut SszError,
) -> u32 {
    // SAFETY: handle and limb borrows remain live outside the scratch suffix;
    // array-pointer cast retains provenance and checks all 32 output bytes.
    unsafe {
        scratch_call(scratch, out32.cast(), error, |arena| {
            proof::node_root(&input_schema(schema)?.desc, input_value(value)?, input_nat(index)?, arena)
        })
    }
}

/// Build a canonical branch in retained caller scratch.
/// # Safety
/// The module-wide C pointer, lifetime, disjointness, and scratch contract applies.
#[no_mangle]
pub unsafe extern "C" fn ssz_build_proof(
    schema: *const SszSchema,
    value: *const SszValue,
    index: SszNat,
    scratch: *mut SszScratch,
    out: *mut SszHashes,
    error: *mut SszError,
) -> u32 {
    // SAFETY: original live handles, valid borrowed limbs, and disjoint writable
    // result/suffix spans are caller obligations; helpers check arithmetic.
    unsafe {
        scratch_call(scratch, out, error, |arena| {
            Ok(output_hashes(proof::build_proof(
                &input_schema(schema)?.desc, input_value(value)?, input_nat(index)?, arena,
            )?))
        })
    }
}

/// Build the canonical descending-helper multiproof in caller scratch.
/// # Safety
/// The module-wide C pointer, lifetime, disjointness, and scratch contract applies.
#[no_mangle]
pub unsafe extern "C" fn ssz_build_multiproof(
    schema: *const SszSchema,
    value: *const SszValue,
    indices: *const SszNat,
    index_count: usize,
    scratch: *mut SszScratch,
    out: *mut SszHashes,
    error: *mut SszError,
) -> u32 {
    // SAFETY: each index record/limb span and original handle stays initialized
    // and immutable; native metadata is allocated only in the disjoint suffix.
    unsafe {
        scratch_call(scratch, out, error, |arena| {
            let schema = input_schema(schema)?;
            let value = input_value(value)?;
            let indices = input_nats(indices, index_count, arena)?;
            Ok(output_hashes(proof::build_multiproof(&schema.desc, value, indices, arena)?))
        })
    }
}

/// Reconstruct a root using raw byte-string operands, without width checks.
/// # Safety
/// The module-wide contract applies; out32 points to 32 disjoint writable bytes.
#[no_mangle]
pub unsafe extern "C" fn ssz_calculate_merkle_root(
    leaf: SszBytes,
    proof: *const SszBytes,
    proof_count: usize,
    index: SszNat,
    scratch: *mut SszScratch,
    out32: *mut u8,
    error: *mut SszError,
) -> u32 {
    // SAFETY: immutable raw node/limb spans obey the recursive input contract;
    // dispatch checks the entire 32-byte output after the provenance-preserving cast.
    unsafe {
        scratch_call(scratch, out32.cast(), error, |arena| {
            let leaf = input_bytes(leaf)?;
            let proof = input_nodes(proof, proof_count, arena)?;
            verify::calculate_merkle_root(leaf, proof, input_nat(index)?, arena)
        })
    }
}

/// Verify node widths and branch structure, then return 0/1 root equality.
/// # Safety
/// The module-wide C pointer, lifetime, disjointness, and scratch contract applies.
#[no_mangle]
pub unsafe extern "C" fn ssz_verify_merkle_proof(
    leaf: SszBytes,
    proof: *const SszBytes,
    proof_count: usize,
    index: SszNat,
    root: SszBytes,
    scratch: *mut SszScratch,
    out: *mut u8,
    error: *mut SszError,
) -> u32 {
    // SAFETY: all referenced input bytes/limbs are immutable and live, and
    // result/error/suffix are disjoint writable storage under the C contract.
    unsafe {
        scratch_call(scratch, out, error, |arena| {
            let leaf = input_bytes(leaf)?;
            let proof = input_nodes(proof, proof_count, arena)?;
            Ok(u8::from(verify::verify_merkle_proof(
                leaf, proof, input_nat(index)?, input_bytes(root)?, arena,
            )?))
        })
    }
}

/// Reconstruct a multiproof root with the core's raw-byte operand semantics.
/// # Safety
/// The module-wide contract applies; out32 points to 32 disjoint writable bytes.
#[no_mangle]
pub unsafe extern "C" fn ssz_calculate_multi_merkle_root(
    leaves: *const SszBytes,
    leaf_count: usize,
    proof: *const SszBytes,
    proof_count: usize,
    indices: *const SszNat,
    index_count: usize,
    scratch: *mut SszScratch,
    out32: *mut u8,
    error: *mut SszError,
) -> u32 {
    // SAFETY: nested input spans remain immutable/live and disjoint from the
    // suffix and outputs; helper conversions validate every active raw span.
    unsafe {
        scratch_call(scratch, out32.cast(), error, |arena| {
            let leaves = input_nodes(leaves, leaf_count, arena)?;
            let proof = input_nodes(proof, proof_count, arena)?;
            let indices = input_nats(indices, index_count, arena)?;
            verify::calculate_multi_merkle_root(leaves, proof, indices, arena)
        })
    }
}

/// Verify all operand widths and multiproof structure, then compare roots.
/// # Safety
/// The module-wide C pointer, lifetime, disjointness, and scratch contract applies.
#[no_mangle]
pub unsafe extern "C" fn ssz_verify_merkle_multiproof(
    leaves: *const SszBytes,
    leaf_count: usize,
    proof: *const SszBytes,
    proof_count: usize,
    indices: *const SszNat,
    index_count: usize,
    root: SszBytes,
    scratch: *mut SszScratch,
    out: *mut u8,
    error: *mut SszError,
) -> u32 {
    // SAFETY: caller retains every node and limb allocation, initializes foreign
    // records, and supplies mutually disjoint mutable outputs/suffix.
    unsafe {
        scratch_call(scratch, out, error, |arena| {
            let leaves = input_nodes(leaves, leaf_count, arena)?;
            let proof = input_nodes(proof, proof_count, arena)?;
            let indices = input_nats(indices, index_count, arena)?;
            Ok(u8::from(verify::verify_merkle_multiproof(
                leaves, proof, indices, input_bytes(root)?, arena,
            )?))
        })
    }
}

/// Calculate SHA-256 without scratch or hidden allocation.
/// # Safety
/// The module-wide contract applies; out32 points to 32 disjoint writable bytes.
#[no_mangle]
pub unsafe extern "C" fn ssz_sha256(input: SszBytes, out32: *mut u8, error: *mut SszError) -> u32 {
    // SAFETY: the caller supplies an immutable input allocation and disjoint
    // writable result/error slots; helpers check their full size and alignment.
    unsafe { dispatch(out32.cast(), error, || Ok(hash::hash(input_bytes(input)?))) }
}

/// Merkleize count consecutive 32-byte chunks, optionally at an arbitrary limit.
/// # Safety
/// The module-wide contract applies; chunks contains count*32 initialized bytes
/// in one allocation, and out32 points to 32 disjoint writable bytes.
#[no_mangle]
pub unsafe extern "C" fn ssz_merkleize(
    chunks: *const u8,
    count: usize,
    has_limit: u32,
    limit: SszNat,
    scratch: *mut SszScratch,
    out32: *mut u8,
    error: *mut SszError,
) -> u32 {
    // SAFETY: [u8; 32] is alignment-one, padding-free, and valid for any 32
    // initialized bytes. input_slice checks count*32 and retains provenance.
    unsafe {
        scratch_call(scratch, out32.cast(), error, |_arena| {
            let limit = match has_limit {
                0 => None,
                1 => Some(input_nat(limit)?),
                _ => return Err(bad_representation()),
            };
            merkle::bounded(input_slice(chunks.cast::<hash::Hash>(), count)?, limit)
        })
    }
}

/// Merkleize count consecutive chunks with the progressive 1,4,16,... spine.
/// # Safety
/// The module-wide contract applies; chunks contains count*32 initialized bytes
/// in one allocation, and out32 points to 32 disjoint writable bytes.
#[no_mangle]
pub unsafe extern "C" fn ssz_merkleize_progressive(
    chunks: *const u8,
    count: usize,
    out32: *mut u8,
    error: *mut SszError,
) -> u32 {
    // SAFETY: the chunk cast preserves provenance with alignment one and the
    // specified 32-byte stride; helpers validate checked size/address arithmetic.
    unsafe {
        dispatch(out32.cast(), error, || {
            Ok(merkle::progressive(input_slice(chunks.cast::<hash::Hash>(), count)?))
        })
    }
}
