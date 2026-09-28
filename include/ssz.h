#ifndef SSZ_FV_H
#define SSZ_FV_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Caller-owned SSZ ABI for Linux x86-64 SysV and AArch64 AAPCS64.
 *
 * Serialization buffers, ordinary result slots, and scratch backing bytes
 * may be uninitialized; output bytes are never read before being written.
 * No allocator, implicit output allocation, or global mutable state is used.
 * Every function returns SSZ_OK or an exact SSZ_* reason below. A non-null
 * error receives that reason and its semantic natural-number/text payloads;
 * success clears it. HOST_* are resource/foreign-representation failures, not
 * SSZ semantic refusals. Ordinary outputs are unchanged on failure, except
 * ssz_serialize may change bytes WITHIN its output capacity (never *written).
 * Scratch.used and error may change even on failure.
 *
 * Every pointer to a struct, array element, handle, or scalar must have its C
 * alignment and refer to a live allocation of readable/writable storage as
 * appropriate. All array byte sizes and pointer+size ranges must fit size_t
 * and PTRDIFF_MAX without wrapping. Nonempty spans require non-null data;
 * zero-length spans may use null data. Required output and input-object
 * pointers must be non-null; only error is optional. Handles must be ones
 * previously returned by this library, not fabricated C objects. JSON graphs
 * must be finite and acyclic, and every struct field must be initialized
 * (inactive JSON fields are ignored). JSON text and field names must be UTF-8.
 * The ABI checks null, alignment and arithmetic, NOT allocation validity or
 * graph acyclicity: those remain caller obligations.
 *
 * Mutable output storage, the scratch descriptor, error, and the available
 * scratch suffix must be mutually disjoint and not overlap any input. Shared
 * immutable inputs are allowed. A registered handle may reside in the USED
 * scratch prefix, never in its available suffix. Concurrent calls may share
 * immutable inputs, but must have disjoint mutable storage.
 *
 * Initialize scratch.used to zero. Calls allocate only [used, capacity),
 * advancing used without invalidating the prefix; require used <= capacity.
 * The backing scratch allocation may be byte-aligned (padding is charged).
 * Handles, JSON views, proof nodes, large natural-number results, and errors
 * can borrow scratch AND original JSON/encoded-byte/natural-limb inputs.
 * Retain all referenced storage unchanged for the full lifetime of every
 * dependent view/handle. Do not reset, reuse, move, or free scratch while
 * those views/handles remain live. There is no handle destructor.
 *
 * The code image must remain immutable and disjoint from writable storage.
 * Ordinary ABI stack space must remain mapped and non-wrapping. The shipped
 * instruction-lowered assembly additionally uses up to 24 bytes below RSP on
 * x86-64 or 576 bytes below SP on AArch64, disjoint from live operand storage.
 * No red zone is used; x86 DF must be clear and ARM SP 16-byte aligned. Recursive
 * types require sufficient ordinary call-stack space as well as caller scratch.
 *
 * Link asm/<arch>/ssz.s with memcpy.s, memset.s, memcmp.s, memmove.s, and
 * udivti3.s from the same directory. No compiler runtime archive is required
 * (see scripts/check-native.py).
 * All five runtime kernels have ISA proofs and assembled-instruction binding.
 * __udivti3 is proved for every nonzero 128-bit divisor, including both return
 * limbs and preservation of memory, SIMD, and callee-saved registers.
 * For fitting byte-vector/list values, memcpy also produces the upstream SSZ
 * encoding. Native validation, dispatch, and decoding are not covered by this
 * bridge; these kernel proofs do not establish whole-library refinement.
 * SHA-256 implementation correctness is a trusted boundary for subsequent
 * hashing/Merkle refinement, not a claimed native proof. Dependent theorems
 * must expose digest correctness against the pinned SHA model and the
 * required ABI/memory-frame guarantees as explicit hypotheses, not axioms.
 * This covers full byte concatenations, including non-32-byte proof nodes;
 * it assumes neither collision-freedom nor correctness of SSZ Merkle logic.
 * Separate algorithm proofs relate packed bits, arbitrary-width integer
 * decoding (including scope rejection), limb conversion/ordering, structural
 * fixed-size measurement, and composite cursor writes to upstream definitions;
 * they do not establish native control-flow or arena-resource refinement.
 * Bit-view algorithm contracts include every scope, padding, delimiter, and
 * capacity rejection, retained packed prefixes, and physical bit-count bounds.
 * External C ABI/schema-wrapper refinement remains open.
 * Arena arithmetic separately proves exact checked-reservation success/failure
 * conditions, alignment, cursor bounds, and zero-length behavior. Integer
 * allocation on both ISAs additionally has native size-check, reservation,
 * and cursor-commit refinement.
 * Both Boolean postdispatch decoder bodies have ISA refinement proofs through
 * their actual stores, register restoration, and return, with results matching
 * upstream Boolean deserialization. The proofs include memory frames and
 * AArch64 lowering-scratch effects. Both bodies have assembly binding;
 * public-ABI dispatch and the remaining native codecs are not covered by
 * these Boolean proofs.
 * Integer decoder instruction images have linked ISA binding, including the
 * AArch64 memcpy call. Checked integer subpaths cover arbitrary-precision
 * descriptor comparison and byte trimming/Small packing on both ISAs, the
 * ARM prefix composed through scope/Small returns or the Large allocation
 * continuation, and allocation with exact arena memory effects on both ISAs.
 * All integer result tails have result, return, and memory-frame proofs,
 * including the linked ARM memcpy. Large packing loops on both ISAs have
 * checked execution and limb-value proofs. Both complete postdispatch UInt
 * bodies are composed through RET, including exact reservation-dependent
 * results and cursor effects under explicit caller ownership. Their arena
 * separation premises permit inputs and existing objects in the used prefix;
 * only the available suffix is reserved for new allocations. Empty input
 * spans impose no separation. Public-ABI dispatch refinement remains open.
 * ByteVector/ByteList instruction images also have linked ISA binding.
 * Both byte-view bodies on both ISAs have postdispatch refinement through
 * RET, including exact upstream results, original input aliasing,
 * saved-register restoration, and memory frames. These contracts
 * allow arbitrary representable Nat capacities, noncanonical Large values,
 * shared immutable inputs, used-prefix storage, and empty input spans.
 * Both standalone Nat.compare callees have checked refinement through RET
 * for arbitrary representable Nats, including shared read-only limbs,
 * saved-register restoration, and the low-byte Ordering result. The x86
 * callee preserves all memory; the ARM callee preserves memory outside its
 * 16-byte lowering slot and retains both borrowed operand observations.
 * Both refinements are root-imported, axiom-audited, and assembly-bound.
 * Delimited-bit decoder images and their Nat.compare callees additionally
 * have joint CodeAt witnesses in a single linked image per ISA, preserving
 * actual relative-call geometry. These witnesses are instruction binding,
 * not complete bit-decoder execution or scratch-resource refinements.
 * A shared executable delimited-decoder algorithm now has checked,
 * root-audited correspondence to both upstream bit-list variants, including
 * exact reservation failure and allocation-before-bound-check effects.
 * Both delimited callees now refine that model through their actual RET,
 * including the linked Nat.compare call, exact scratch failure/commit effects,
 * original inputs, and ABI/memory frames. Their execution theorems and
 * BitList/ProgressiveBitList SSZ corollaries are root-imported and axiom-audited.
 * Public dispatch wrappers remain open.
 * Both private Nat.div_rem_small helpers have complete entry-through-RET
 * refinement, including their actual __udivti3 calls, for divisors >= 2.
 * Their contracts retain exact quotient/remainder, all scratch writes,
 * cursor effects, original operand representations, and ABI/memory frames.
 * Nat.add, Nat.to_u128, and codec::exact are also proved on both ISAs.
 * These helper theorems are root-imported and axiom-audited.
 * Both private Nat.from_u128 constructors have root-audited actual
 * entry-through-RET refinement against the checked fromWide model, including
 * allocation guards, both complete limbs, exact cursor/result writes, and
 * ABI/memory frames. Their Small-path theorems require no arena ownership.
 * The ARM frame includes its actual SP-16 lowering scratch. Both actual
 * constructor images have instruction-binding witnesses.
 * BitVector has root-audited postdispatch-through-RET refinement on both ISAs:
 * all helper calls and branches, both complete scratch allocations retained
 * on failure, exact cursor effects, zero-copy results, original inputs, and
 * ABI frames. The external C ABI/schema wrapper remains outside this coverage.
 * Both ISAs' BitList and ProgressiveBitList wrappers have root-audited
 * postdispatch-through-RET refinement, including the actual progressive
 * tail call and arbitrary optional-cap representations.
 * Both ISAs' Bool, UInt, ByteVector, ByteList, BitVector, BitList, and
 * ProgressiveBitList additionally have root-audited refinement from the
 * actual private decoder entry, including its prologue and tag dispatch,
 * through the original caller return. These are the seven primitive tags;
 * composite decoders, serialization, and the external C/schema wrapper
 * are not covered by these entry proofs.
 * Separate executable-model proofs now cover primitive measurement, encoded
 * size, serialization, and allocating serialization against pinned SSZ,
 * including exact resource failures, ordered scratch effects/no rollback,
 * output prefix initialization, untouched tails, and no output-content reads.
 * Both roots audit these logical contracts; serializer ISA execution,
 * concrete memory/provenance, and ABI refinement remain open.
 *
 * Executing this ABI on both targets is runtime evidence, not an ISA proof.
 */

typedef struct ssz_bytes {
    const uint8_t *data;
    size_t len;
} ssz_bytes;

/* limb_count == 0 uses small. Otherwise limbs are little-endian base-2^64,
 * small is ignored, and leading zero limbs are permitted. Logical SSZ
 * capacities and indices have no uint64_t/size_t limit. */
typedef struct ssz_nat {
    uint64_t small;
    const uint64_t *limbs;
    size_t limb_count;
} ssz_nat;

typedef struct ssz_scratch {
    uint8_t *data;
    size_t capacity;
    size_t used;
} ssz_scratch;

typedef struct ssz_error {
    uint32_t reason;
    ssz_nat args[3];
    ssz_bytes text;
} ssz_error;

enum ssz_reason {
    SSZ_OK = 0,
    SSZ_WRONG_TYPE = 1,
    SSZ_LIMIT = 2,
    SSZ_SCOPE = 3,
    SSZ_SCOPE_TOO_SMALL = 4,
    SSZ_SCOPE_UNDIVIDED = 5,
    SSZ_SCOPE_WIDTHLESS = 6,
    SSZ_FIRST_OFFSET = 7,
    SSZ_OFFSET_UNORDERED = 8,
    SSZ_OFFSET_PAST_SCOPE = 9,
    SSZ_OFFSET_UNALIGNED = 10,
    SSZ_OFFSET_BELOW_TABLE = 11,
    SSZ_TRUNCATED = 12,
    SSZ_NOT_A_BIT = 13,
    SSZ_COUNT = 14,
    SSZ_PADDING_BITS = 15,
    SSZ_EMPTY_ENCODING = 16,
    SSZ_NO_DELIMITER = 17,
    SSZ_TRAILING_ZEROS = 18,
    SSZ_NO_SELECTOR = 19,
    SSZ_UNKNOWN_SELECTOR = 20,
    SSZ_OFFSET_OVERFLOW = 21,
    SSZ_BAD_DECLARATION = 22,
    SSZ_NOT_A_POSITION = 23,
    SSZ_NOT_ENTITLED = 24,
    SSZ_UNDECLARED = 25,
    SSZ_CAPACITY_NEGATIVE = 26,
    SSZ_LAYOUT_NOT_BITS = 27,
    SSZ_VECTOR_EMPTY = 28,
    SSZ_LAYOUT_WIDTH = 29,
    SSZ_LAYOUT_TRAILING_GAP = 30,
    SSZ_LAYOUT_TOO_WIDE = 31,
    SSZ_LAYOUT_FIELD_COUNT = 32,
    SSZ_UNION_EMPTY = 33,
    SSZ_UNION_SELECTOR_RANGE = 34,
    SSZ_UNION_INCOMPATIBLE = 35,
    SSZ_UNION_SELECTOR_REPEATED = 36,
    SSZ_UINT_WIDTH = 37,
    SSZ_CONTAINER_EMPTY = 38,
    SSZ_NOT_A_GINDEX = 39,
    SSZ_ROOT_HAS_NO_BRANCH = 40,
    SSZ_EMPTY_REQUEST = 41,
    SSZ_REPEATED_INDEX = 42,
    SSZ_NESTED_INDEX = 43,
    SSZ_BRANCH_LENGTH = 44,
    SSZ_LEAF_COUNT = 45,
    SSZ_PROOF_LENGTH = 46,
    SSZ_PROOF_INCOMPLETE = 47,
    SSZ_PATH_INTO_MIXIN = 48,
    SSZ_PATH_INTO_PACKED = 49,
    SSZ_PATH_INTO_GAP = 50,
    SSZ_PATH_PAST_SPINE = 51,
    SSZ_NO_PARTS = 52,
    SSZ_NO_PARTS_MIXIN = 53,
    SSZ_NO_MIXIN = 54,
    SSZ_NO_CHUNK_COUNT = 55,
    SSZ_NOT_STEPPABLE = 56,
    SSZ_NO_SUCH_FIELD = 57,
    SSZ_NO_SUCH_OPTION = 58,
    SSZ_NO_SUCH_POSITION = 59,
    SSZ_MERKLEIZE_LIMIT = 60,
    SSZ_ZERO_TREE_WIDTH = 61,
    SSZ_HEX_PREFIX = 62,
    SSZ_HEX_DIGITS = 63,
    SSZ_HEX_LENGTH = 64,
    SSZ_BITFIELD_PADDING = 65,
    SSZ_BITFIELD_DELIMITER = 66,
    SSZ_BITFIELD_TRAILING_ZEROS = 67,
    SSZ_UINT_RANGE = 68,
    SSZ_OVER_LIMIT = 69,
    SSZ_ELEMENT_KIND = 70,
    SSZ_NO_DEFAULT = 71,
    SSZ_UNDECLARED_FIELD = 72,
    SSZ_MISSING_FIELD = 73,
    SSZ_STRUCT_NOT_AN_OBJECT = 74,
    SSZ_UNDECLARED_SELECTOR = 75,
    SSZ_HOST_SCRATCH_EXHAUSTED = 0x8000,
    SSZ_HOST_OUTPUT_TOO_SMALL = 0x8001,
    SSZ_HOST_BAD_REPRESENTATION = 0x8002
};

enum ssz_json_tag {
    SSZ_JSON_NULL = 0,
    SSZ_JSON_BOOL = 1,
    SSZ_JSON_NUMBER = 2,
    SSZ_JSON_STRING = 3,
    SSZ_JSON_ARRAY = 4,
    SSZ_JSON_OBJECT = 5
};

typedef struct ssz_json ssz_json;
typedef struct ssz_json_field ssz_json_field;
struct ssz_json {
    uint32_t tag;
    uint32_t boolean; /* BOOL only; exactly 0 or 1 */
    ssz_bytes text;   /* NUMBER: original numeric token, never a float conversion */
    const ssz_json *items;
    size_t item_count;
    const ssz_json_field *fields;
    size_t field_count;
};
struct ssz_json_field {
    ssz_bytes name;
    ssz_json value;
};
/* Objects use last-duplicate-wins and sorted-name semantics. */

typedef struct ssz_schema ssz_schema;
typedef struct ssz_value ssz_value;
typedef struct ssz_hashes {
    const uint8_t *data; /* count consecutive 32-byte hashes */
    size_t count;
} ssz_hashes;

enum ssz_path_format {
    SSZ_PATH_INDEX = 0, /* array of field strings, position numbers, {mixin: ...} */
    SSZ_PATH_PROOF = 1  /* array of {field: ...}, {position: ...}, {mixin: ...} */
};

uint32_t ssz_schema_from_json(const ssz_json *document, ssz_scratch *scratch,
    const ssz_schema **out, ssz_error *error);
uint32_t ssz_value_from_json(const ssz_schema *schema, const ssz_json *document,
    ssz_scratch *scratch, const ssz_value **out, ssz_error *error);
uint32_t ssz_value_to_json(const ssz_schema *schema, const ssz_value *value,
    ssz_scratch *scratch, const ssz_json **out, ssz_error *error);
uint32_t ssz_default_value(const ssz_schema *schema, ssz_scratch *scratch,
    const ssz_value **out, ssz_error *error);
uint32_t ssz_is_zero(const ssz_schema *schema, const ssz_value *value,
    ssz_scratch *scratch, uint8_t *out, ssz_error *error);
uint32_t ssz_compatible(const ssz_schema *left, const ssz_schema *right,
    uint8_t *out, ssz_error *error);
uint32_t ssz_serialize(const ssz_schema *schema, const ssz_value *value,
    uint8_t *output, size_t capacity, ssz_scratch *scratch,
    size_t *written, ssz_error *error);
uint32_t ssz_deserialize(const ssz_schema *schema, ssz_bytes input,
    ssz_scratch *scratch, const ssz_value **out, ssz_error *error);
/* Every out32 below points to at least 32 writable bytes. */
uint32_t ssz_hash_tree_root(const ssz_schema *schema, const ssz_value *value,
    ssz_scratch *scratch, uint8_t *out32, ssz_error *error);
uint32_t ssz_generalized_index(const ssz_schema *schema, const ssz_json *path,
    uint32_t proof_format, ssz_scratch *scratch, ssz_nat *out, ssz_error *error);
uint32_t ssz_node_root(const ssz_schema *schema, const ssz_value *value,
    ssz_nat index, ssz_scratch *scratch, uint8_t *out32, ssz_error *error);
/* Branch order is leaf-to-root. Multiproof nodes follow descending helper
 * indices; leaves stay paired with the caller's indices, not sorted in place.
 * Node reads permit index 1; branch/proof requests reject root/zero indices. */
uint32_t ssz_build_proof(const ssz_schema *schema, const ssz_value *value,
    ssz_nat index, ssz_scratch *scratch, ssz_hashes *out, ssz_error *error);
uint32_t ssz_build_multiproof(const ssz_schema *schema, const ssz_value *value,
    const ssz_nat *indices, size_t index_count, ssz_scratch *scratch,
    ssz_hashes *out, ssz_error *error);
/* Raw calculators hash arbitrary-width byte operands. Verifiers require
 * 32-byte leaves, roots, and proof nodes. A well-formed proof of a wrong root
 * returns SSZ_OK with *out == 0; malformed structure returns an error and
 * leaves *out unchanged. Boolean outputs are always exactly 0 or 1. */
uint32_t ssz_calculate_merkle_root(ssz_bytes leaf, const ssz_bytes *proof,
    size_t proof_count, ssz_nat index, ssz_scratch *scratch,
    uint8_t *out32, ssz_error *error);
uint32_t ssz_verify_merkle_proof(ssz_bytes leaf, const ssz_bytes *proof,
    size_t proof_count, ssz_nat index, ssz_bytes root, ssz_scratch *scratch,
    uint8_t *out, ssz_error *error);
uint32_t ssz_calculate_multi_merkle_root(const ssz_bytes *leaves,
    size_t leaf_count, const ssz_bytes *proof, size_t proof_count,
    const ssz_nat *indices, size_t index_count, ssz_scratch *scratch,
    uint8_t *out32, ssz_error *error);
uint32_t ssz_verify_merkle_multiproof(const ssz_bytes *leaves,
    size_t leaf_count, const ssz_bytes *proof, size_t proof_count,
    const ssz_nat *indices, size_t index_count, ssz_bytes root,
    ssz_scratch *scratch, uint8_t *out, ssz_error *error);
uint32_t ssz_sha256(ssz_bytes input, uint8_t *out32, ssz_error *error);
/* chunks contains count * 32 bytes. has_limit must be exactly 0 or 1;
 * limit is ignored when has_limit == 0. */
uint32_t ssz_merkleize(const uint8_t *chunks, size_t count, uint32_t has_limit,
    ssz_nat limit, ssz_scratch *scratch, uint8_t *out32, ssz_error *error);
uint32_t ssz_merkleize_progressive(const uint8_t *chunks, size_t count,
    uint8_t *out32, ssz_error *error);

#ifdef __cplusplus
}
#endif
#endif
