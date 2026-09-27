#include "ssz.h"

void smoke_write(const char *, size_t);
void *memcpy(void *restrict, const void *restrict, size_t);
void *memmove(void *, const void *, size_t);
void *memset(void *, int, size_t);
int memcmp(const void *, const void *, size_t);

#define COUNT(a) (sizeof(a) / sizeof((a)[0]))
#define BYTES(a) ((ssz_bytes){(const uint8_t *)(a), sizeof(a)})
#define TEXT(s) {(const uint8_t *)(s), sizeof(s) - 1}
#define NAT(n) ((ssz_nat){(n), NULL, 0})
#define STRING(s) {.tag=SSZ_JSON_STRING,.text=TEXT(s)}
#define NUMBER(s) {.tag=SSZ_JSON_NUMBER,.text=TEXT(s)}
#define ARRAY(a) {.tag=SSZ_JSON_ARRAY,.items=(a),.item_count=COUNT(a)}
#define OBJECT(a) {.tag=SSZ_JSON_OBJECT,.fields=(a),.field_count=COUNT(a)}

enum fixture_format { FIX_CODEC, FIX_JSON, FIX_GINDEX, FIX_SCHEMA, FIX_PROOF, FIX_MULTI };
struct fixture {
    const char *name;
    enum fixture_format format;
    uint32_t valid, reason;
    ssz_json schema, value, path;
    ssz_bytes encoded, root, leaf;
    ssz_nat index;
    const ssz_bytes *nodes, *leaves;
    size_t nodes_count, leaves_count;
    const ssz_nat *indices;
    size_t indices_count;
    const ssz_json *paths;
    size_t paths_count;
};
#include "fixtures.h"

static _Alignas(16) uint8_t storage[32 * 1024 * 1024];
static uint8_t encoding[MAX_ENCODED + 32];
static ssz_scratch arena;
static ssz_error error;
static uint32_t actual_status, expected_status;
static const char *case_name;

static void text(const char *s) {
    size_t n = 0;
    while (s[n]) ++n;
    smoke_write(s, n);
}
static void decimal(size_t n) {
    char digits[32];
    size_t end = sizeof(digits), start = end;
    do { digits[--start] = (char)('0' + n % 10); n /= 10; } while (n);
    smoke_write(digits + start, end - start);
}
static int failure(unsigned line, const char *condition) {
    text("FAIL "); text(case_name); text(" at smoke.c:"); decimal(line);
    text(" "); text(condition); text(" (status "); decimal(actual_status);
    text(", expected "); decimal(expected_status); text(")\n");
    return 1;
}
#define CHECK(c) do { if (!(c)) return failure(__LINE__, #c); } while (0)
#define EXPECT(call, status) do { expected_status = (status); actual_status = (call); \
    CHECK(actual_status == expected_status); CHECK(error.reason == expected_status); } while (0)
#define OK(call) EXPECT(call, SSZ_OK)

static int equal(ssz_bytes a, ssz_bytes b) {
    return a.len == b.len && (a.len == 0 || memcmp(a.data, b.data, a.len) == 0);
}
static int filled(const uint8_t *data, size_t count, uint8_t byte) {
    for (size_t i = 0; i < count; ++i) if (data[i] != byte) return 0;
    return 1;
}
static uint64_t word(ssz_nat n, size_t i) {
    return n.limb_count ? (i < n.limb_count ? n.limbs[i] : 0) : (i == 0 ? n.small : 0);
}
static int same_nat(ssz_nat a, ssz_nat b) {
    size_t count = a.limb_count > b.limb_count ? a.limb_count : b.limb_count;
    if (count == 0) count = 1;
    for (size_t i = 0; i < count; ++i) if (word(a, i) != word(b, i)) return 0;
    return 1;
}
static int same_json(const ssz_json *a, const ssz_json *b) {
    if (a->tag != b->tag) return 0;
    switch (a->tag) {
    case SSZ_JSON_NULL: return 1;
    case SSZ_JSON_BOOL: return a->boolean == b->boolean;
    case SSZ_JSON_NUMBER: case SSZ_JSON_STRING: return equal(a->text, b->text);
    case SSZ_JSON_ARRAY:
        if (a->item_count != b->item_count) return 0;
        for (size_t i = 0; i < a->item_count; ++i)
            if (!same_json(&a->items[i], &b->items[i])) return 0;
        return 1;
    case SSZ_JSON_OBJECT:
        if (a->field_count != b->field_count) return 0;
        for (size_t i = 0; i < a->field_count; ++i) {
            size_t j = 0;
            while (j < b->field_count && !equal(a->fields[i].name, b->fields[j].name)) ++j;
            if (j == b->field_count || !same_json(&a->fields[i].value, &b->fields[j].value)) return 0;
        }
        return 1;
    default: return 0;
    }
}
static int same_nodes(ssz_hashes got, const ssz_bytes *want, size_t count) {
    if (got.count != count) return 0;
    for (size_t i = 0; i < count; ++i)
        if (!equal((ssz_bytes){got.data + 32 * i, 32}, want[i])) return 0;
    return 1;
}
static void reset_arena(void) {
    /* Previous case's handles/views are no longer used after this point. */
    arena = (ssz_scratch){storage, sizeof(storage), 0};
}
static int encoded(const ssz_schema *schema, const ssz_value *value, ssz_bytes want) {
    size_t written = SIZE_MAX;
    memset(encoding, 0xa5, sizeof(encoding));
    OK(ssz_serialize(schema, value, encoding + 8, want.len, &arena, &written, &error));
    CHECK(written == want.len);
    CHECK(equal((ssz_bytes){encoding + 8, written}, want));
    CHECK(filled(encoding, 8, 0xa5));
    CHECK(filled(encoding + 8 + written, sizeof(encoding) - 8 - written, 0xa5));
    if (want.len != 0) {
        memset(encoding, 0xa5, sizeof(encoding));
        written = SIZE_MAX;
        EXPECT(ssz_serialize(schema, value, encoding + 8, want.len - 1,
            &arena, &written, &error), SSZ_HOST_OUTPUT_TOO_SMALL);
        CHECK(written == SIZE_MAX);
        CHECK(filled(encoding, 8, 0xa5));
        CHECK(filled(encoding + 8 + want.len - 1, sizeof(encoding) - 8 - want.len + 1, 0xa5));
    }
    return 0;
}

static int fixture(const struct fixture *f) {
    reset_arena();
    const ssz_schema *schema = NULL;
    const ssz_value *value = NULL, *decoded = NULL;
    const ssz_json *document = NULL;
    uint8_t root[32], verdict = 0xa5;
    ssz_nat index = NAT(999);
    ssz_hashes built = {NULL, 0};
    if (f->format == FIX_SCHEMA) {
        EXPECT(ssz_schema_from_json(&f->schema, &arena, &schema, &error), f->reason);
        CHECK(schema == NULL);
        return 0;
    }
    OK(ssz_schema_from_json(&f->schema, &arena, &schema, &error));
    if (f->format == FIX_GINDEX) {
        EXPECT(ssz_generalized_index(schema, &f->path, SSZ_PATH_INDEX,
            &arena, &index, &error), f->reason);
        CHECK(same_nat(index, f->valid ? f->index : NAT(999)));
        return 0;
    }
    if (f->format == FIX_CODEC && !f->valid) {
        EXPECT(ssz_deserialize(schema, f->encoded, &arena, &decoded, &error), f->reason);
        CHECK(decoded == NULL);
        return 0;
    }
    if (f->format == FIX_JSON && !f->valid) {
        EXPECT(ssz_value_from_json(schema, &f->value, &arena, &value, &error), f->reason);
        CHECK(value == NULL);
        return 0;
    }
    OK(ssz_value_from_json(schema, &f->value, &arena, &value, &error));
    if (encoded(schema, value, f->encoded)) return 1;
    OK(ssz_deserialize(schema, f->encoded, &arena, &decoded, &error));
    if (encoded(schema, decoded, f->encoded)) return 1;
    if (f->format == FIX_JSON) {
        OK(ssz_value_to_json(schema, value, &arena, &document, &error));
        CHECK(same_json(document, &f->value));
        OK(ssz_value_to_json(schema, decoded, &arena, &document, &error));
        CHECK(same_json(document, &f->value));
        return 0;
    }
    OK(ssz_hash_tree_root(schema, value, &arena, root, &error));
    CHECK(equal(BYTES(root), f->root));
    OK(ssz_hash_tree_root(schema, decoded, &arena, root, &error));
    CHECK(equal(BYTES(root), f->root));
    if (f->format == FIX_CODEC) return 0;
    if (f->format == FIX_PROOF) {
        OK(ssz_generalized_index(schema, &f->path, SSZ_PATH_PROOF, &arena, &index, &error));
        CHECK(same_nat(index, f->index));
        if (f->leaf.data == NULL) {
            memset(root, 0xa5, sizeof(root));
            EXPECT(ssz_node_root(schema, value, index, &arena, root, &error), f->reason);
            CHECK(filled(root, sizeof(root), 0xa5));
            return 0;
        }
        EXPECT(ssz_verify_merkle_proof(f->leaf, f->nodes, f->nodes_count,
            index, f->root, &arena, &verdict, &error), f->reason);
        CHECK(verdict == (f->reason ? 0xa5 : f->valid));
        if (!f->valid) return 0;
        OK(ssz_node_root(schema, value, index, &arena, root, &error));
        CHECK(equal(BYTES(root), f->leaf));
        OK(ssz_build_proof(schema, value, index, &arena, &built, &error));
        CHECK(same_nodes(built, f->nodes, f->nodes_count));
        OK(ssz_calculate_merkle_root(f->leaf, f->nodes, f->nodes_count, index, &arena, root, &error));
        CHECK(equal(BYTES(root), f->root));
        root[0] ^= 1;
        OK(ssz_verify_merkle_proof(f->leaf, f->nodes, f->nodes_count,
            index, BYTES(root), &arena, &verdict, &error));
        CHECK(verdict == 0);
        CHECK(same_nodes(built, f->nodes, f->nodes_count)); /* append preserves view */
        return 0;
    }
    CHECK(f->format == FIX_MULTI && f->paths_count == f->indices_count);
    for (size_t i = 0; i < f->paths_count; ++i) {
        OK(ssz_generalized_index(schema, &f->paths[i], SSZ_PATH_PROOF, &arena, &index, &error));
        CHECK(same_nat(index, f->indices[i]));
    }
    EXPECT(ssz_verify_merkle_multiproof(f->leaves, f->leaves_count,
        f->nodes, f->nodes_count, f->indices, f->indices_count, f->root,
        &arena, &verdict, &error), f->reason);
    CHECK(verdict == (f->reason ? 0xa5 : f->valid));
    if (!f->valid) return 0;
    OK(ssz_build_multiproof(schema, value, f->indices, f->indices_count, &arena, &built, &error));
    CHECK(same_nodes(built, f->nodes, f->nodes_count));
    for (size_t i = 0; i < f->indices_count; ++i) {
        OK(ssz_node_root(schema, value, f->indices[i], &arena, root, &error));
        CHECK(equal(BYTES(root), f->leaves[i]));
    }
    OK(ssz_calculate_multi_merkle_root(f->leaves, f->leaves_count, f->nodes,
        f->nodes_count, f->indices, f->indices_count, &arena, root, &error));
    CHECK(equal(BYTES(root), f->root));
    root[0] ^= 1;
    OK(ssz_verify_merkle_multiproof(f->leaves, f->leaves_count, f->nodes,
        f->nodes_count, f->indices, f->indices_count, BYTES(root), &arena, &verdict, &error));
    CHECK(verdict == 0);
    CHECK(same_nodes(built, f->nodes, f->nodes_count));
    /* Leaves stay paired with their requested indices, not sorted in place. */
    ssz_nat reversed_indices[f->indices_count];
    ssz_bytes reversed_leaves[f->leaves_count];
    for (size_t i = 0; i < f->indices_count; ++i) {
        reversed_indices[i] = f->indices[f->indices_count-1-i];
        reversed_leaves[i] = f->leaves[f->leaves_count-1-i];
    }
    OK(ssz_verify_merkle_multiproof(reversed_leaves, f->leaves_count, f->nodes,
        f->nodes_count, reversed_indices, f->indices_count, f->root, &arena, &verdict, &error));
    CHECK(verdict == 1);
    if (f->nodes_count > 1) {
        size_t other = 1;
        while (other < f->nodes_count && equal(f->nodes[0], f->nodes[other])) ++other;
        if (other < f->nodes_count) {
            ssz_bytes reversed_nodes[f->nodes_count];
            for (size_t i = 0; i < f->nodes_count; ++i) reversed_nodes[i] = f->nodes[i];
            reversed_nodes[0] = f->nodes[other];
            reversed_nodes[other] = f->nodes[0];
            OK(ssz_verify_merkle_multiproof(f->leaves, f->leaves_count, reversed_nodes,
                f->nodes_count, f->indices, f->indices_count, f->root, &arena, &verdict, &error));
            CHECK(verdict == 0); /* structurally valid, wrong helper order */
        }
    }
    return 0;
}

static int hash_answers(void) {
    /* FIPS 180-4/NIST SHA-256 known answers: empty, abc, two-block padding,
     * and one million 'a' bytes exercise independent boundary conditions. */
    static const struct { const char *message, *hex; } vectors[] = {
        {"", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"},
        {"abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"},
        {"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
         "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"},
        {NULL, "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"}
    };
    static uint8_t million[1000000];
    uint8_t guarded[40];
    for (size_t i = 0; i < COUNT(vectors); ++i) {
        ssz_bytes input = {NULL, 0};
        if (vectors[i].message) {
            input.data = (const uint8_t *)vectors[i].message;
            while (input.data[input.len]) ++input.len;
            if (input.len == 0) input.data = NULL;
        } else {
            memset(million, 'a', sizeof(million));
            input = BYTES(million);
        }
        memset(guarded, 0xa5, sizeof(guarded));
        OK(ssz_sha256(input, guarded + 4, &error));
        CHECK(filled(guarded, 4, 0xa5) && filled(guarded + 36, 4, 0xa5));
        for (size_t j = 0; j < 32; ++j) {
            char high = vectors[i].hex[2*j], low = vectors[i].hex[2*j+1];
            unsigned a = high <= '9' ? (unsigned)(high-'0') : (unsigned)(high-'a'+10);
            unsigned b = low <= '9' ? (unsigned)(low-'0') : (unsigned)(low-'a'+10);
            CHECK(guarded[4+j] == 16*a+b);
        }
    }
    /* Raw branch reconstruction hashes "a" || "bc" at index two, whereas
     * the verifier rejects these operand widths before proof structure. */
    ssz_bytes leaf = TEXT("a"), sibling = TEXT("bc");
    uint8_t root[32], expected[32], verdict = 0xa5;
    ssz_bytes abc = TEXT("abc");
    reset_arena();
    OK(ssz_sha256(abc, expected, &error)); /* already checked against published answer */
    OK(ssz_calculate_merkle_root(leaf, &sibling, 1, NAT(2), &arena, root, &error));
    CHECK(equal(BYTES(root), BYTES(expected)));
    EXPECT(ssz_verify_merkle_proof(leaf, &sibling, 1, NAT(2), BYTES(root),
        &arena, &verdict, &error), SSZ_COUNT);
    CHECK(verdict == 0xa5 && same_nat(error.args[0], NAT(32)) && same_nat(error.args[1], NAT(1)));
    ssz_nat index = NAT(2);
    OK(ssz_calculate_multi_merkle_root(&leaf, 1, &sibling, 1, &index, 1, &arena, root, &error));
    CHECK(equal(BYTES(root), BYTES(expected)));
    EXPECT(ssz_verify_merkle_multiproof(&leaf, 1, &sibling, 1, &index, 1,
        BYTES(root), &arena, &verdict, &error), SSZ_COUNT);
    CHECK(verdict == 0xa5);
    return 0;
}

static int merkle_and_wide_metadata(void) {
    uint8_t chunks[6][32], root[32], verdict = 0xa5;
    static const uint8_t zero[32] = {0};
    for (size_t i = 0; i < 6; ++i) memset(chunks[i], (int)i + 1, 32);
    reset_arena();
    OK(ssz_merkleize(&chunks[0][0], 3, 0, NAT(0), &arena, root, &error));
    CHECK(equal(BYTES(root), BYTES(bounded_answer)));
    OK(ssz_merkleize(&chunks[0][0], 3, 1, NAT(4), &arena, root, &error));
    CHECK(equal(BYTES(root), BYTES(bounded_answer)));
    memset(root, 0xa5, sizeof(root));
    EXPECT(ssz_merkleize(&chunks[0][0], 3, 1, NAT(2), &arena, root, &error), SSZ_MERKLEIZE_LIMIT);
    CHECK(filled(root, 32, 0xa5) && same_nat(error.args[0], NAT(3)) && same_nat(error.args[1], NAT(2)));
    OK(ssz_merkleize_progressive(&chunks[0][0], 6, root, &error));
    CHECK(equal(BYTES(root), BYTES(progressive_answer)));
    OK(ssz_merkleize_progressive(NULL, 0, root, &error));
    CHECK(equal(BYTES(root), BYTES(zero)));
    static const uint64_t capacity_limbs[] = {0, 65536, 0}; /* 2^80, redundant zero limb */
    const ssz_nat capacity = {123, capacity_limbs, COUNT(capacity_limbs)};
    OK(ssz_merkleize(NULL, 0, 1, capacity, &arena, root, &error));
    CHECK(equal(BYTES(root), BYTES(wide_zero_answer)));

    static const ssz_json_field fields[] = {
        {TEXT("kind"), STRING("ByteList")},
        {TEXT("limit"), NUMBER("1208925819614629174706176")}
    };
    static const ssz_json schema_document = OBJECT(fields);
    static const ssz_json path_items[] = {NUMBER("604462909807314587353088")};
    static const ssz_json path = ARRAY(path_items);
    static const ssz_json bad_path_items[] = {NUMBER("1208925819614629174706176")};
    static const ssz_json bad_path = ARRAY(bad_path_items);
    static const ssz_json empty_bytes = STRING("0x");
    const ssz_schema *schema = NULL;
    const ssz_value *value = NULL;
    ssz_nat index = NAT(777);
    ssz_hashes branch = {NULL, 0};
    OK(ssz_schema_from_json(&schema_document, &arena, &schema, &error));
    OK(ssz_value_from_json(schema, &empty_bytes, &arena, &value, &error));
    OK(ssz_generalized_index(schema, &path, SSZ_PATH_INDEX, &arena, &index, &error));
    static const uint64_t index_limbs[] = {0, 5120}; /* 2^76 + 2^74 */
    const ssz_nat expected_index = {0, index_limbs, COUNT(index_limbs)};
    CHECK(same_nat(index, expected_index));
    size_t held_used = arena.used;
    EXPECT(ssz_generalized_index(schema, &bad_path, SSZ_PATH_INDEX, &arena, &index, &error), SSZ_NO_SUCH_POSITION);
    CHECK(same_nat(index, expected_index) && same_nat(error.args[0], capacity));
    CHECK(arena.used >= held_used && arena.used <= arena.capacity);
    OK(ssz_hash_tree_root(schema, value, &arena, root, &error));
    CHECK(equal(BYTES(root), BYTES(wide_list_answer)));
    OK(ssz_node_root(schema, value, index, &arena, root, &error));
    CHECK(equal(BYTES(root), BYTES(zero)));
    OK(ssz_build_proof(schema, value, index, &arena, &branch, &error));
    CHECK(branch.count == 76);
    ssz_bytes nodes[76];
    for (size_t i = 0; i < 76; ++i) nodes[i] = (ssz_bytes){branch.data + 32*i, 32};
    OK(ssz_calculate_merkle_root(BYTES(zero), nodes, COUNT(nodes), index, &arena, root, &error));
    CHECK(equal(BYTES(root), BYTES(wide_list_answer)));
    OK(ssz_verify_merkle_proof(BYTES(zero), nodes, COUNT(nodes), index,
        BYTES(wide_list_answer), &arena, &verdict, &error));
    CHECK(verdict == 1);
    verdict = 0xa5;
    EXPECT(ssz_verify_merkle_proof(BYTES(zero), nodes, COUNT(nodes)-1, index,
        BYTES(wide_list_answer), &arena, &verdict, &error), SSZ_BRANCH_LENGTH);
    CHECK(verdict == 0xa5 && same_nat(error.args[0], NAT(76)) && same_nat(error.args[1], NAT(75)));
    return 0;
}

static int resources_and_defaults(void) {
    static const ssz_json_field scalar_fields[] = {
        {TEXT("kind"), STRING("Uint256")}, {TEXT("bits"), NUMBER("256")}
    };
    static const ssz_json scalar = OBJECT(scalar_fields);
    static const ssz_json_field bool_fields[] = {{TEXT("kind"), STRING("Boolean")}};
    static const ssz_json boolean = OBJECT(bool_fields);
    static const ssz_json one = STRING("1");
    static const ssz_json zero_json = STRING("0");
    static const uint8_t zero[32] = {0};
    reset_arena();
    const ssz_schema *schema = NULL, *bool_schema = NULL;
    const ssz_value *default_value = NULL, *value = NULL;
    const ssz_json *json = NULL;
    uint8_t verdict = 0xa5, root[32];
    OK(ssz_schema_from_json(&scalar, &arena, &schema, &error));
    OK(ssz_schema_from_json(&boolean, &arena, &bool_schema, &error));
    OK(ssz_default_value(schema, &arena, &default_value, &error));
    OK(ssz_is_zero(schema, default_value, &arena, &verdict, &error));
    CHECK(verdict == 1);
    OK(ssz_value_to_json(schema, default_value, &arena, &json, &error));
    CHECK(same_json(json, &zero_json));
    OK(ssz_hash_tree_root(schema, default_value, &arena, root, &error));
    CHECK(equal(BYTES(root), BYTES(zero)));
    OK(ssz_value_from_json(schema, &one, &arena, &value, &error));
    OK(ssz_is_zero(schema, value, &arena, &verdict, &error));
    CHECK(verdict == 0);
    OK(ssz_compatible(schema, schema, &verdict, &error));
    CHECK(verdict == 1);
    OK(ssz_compatible(schema, bool_schema, &verdict, &error));
    CHECK(verdict == 0);

    uint8_t tiny_memory[64];
    memset(tiny_memory, 0xa5, sizeof(tiny_memory));
    ssz_scratch tiny = {tiny_memory + 8, 17, 16};
    const ssz_schema *unchanged = schema;
    EXPECT(ssz_schema_from_json(&scalar, &tiny, &unchanged, &error), SSZ_HOST_SCRATCH_EXHAUSTED);
    CHECK(unchanged == schema && tiny.used >= 16 && tiny.used <= 17);
    CHECK(filled(tiny_memory, 24, 0xa5) && filled(tiny_memory + 25, 39, 0xa5));
    tiny = (ssz_scratch){NULL, 0, 0};
    const ssz_value *unchanged_value = value;
    EXPECT(ssz_default_value(schema, &tiny, &unchanged_value, &error), SSZ_HOST_SCRATCH_EXHAUSTED);
    CHECK(unchanged_value == value && tiny.used == 0);
    tiny = (ssz_scratch){tiny_memory, sizeof(tiny_memory), sizeof(tiny_memory)+1};
    EXPECT(ssz_default_value(schema, &tiny, &unchanged_value, &error), SSZ_HOST_BAD_REPRESENTATION);
    CHECK(unchanged_value == value);

    static const uint8_t invalid_boolean[] = {2};
    EXPECT(ssz_deserialize(bool_schema, BYTES(invalid_boolean), &arena,
        &unchanged_value, &error), SSZ_NOT_A_BIT);
    CHECK(unchanged_value == value && same_nat(error.args[0], NAT(2)));
    memset(root, 0xa5, sizeof(root));
    EXPECT(ssz_sha256((ssz_bytes){NULL, 1}, root, &error), SSZ_HOST_BAD_REPRESENTATION);
    CHECK(filled(root, sizeof(root), 0xa5));
    ssz_nat out = NAT(123);
    static const ssz_json empty_path = {.tag=SSZ_JSON_ARRAY};
    EXPECT(ssz_generalized_index(schema, &empty_path, 2, &arena, &out, &error), SSZ_HOST_BAD_REPRESENTATION);
    CHECK(same_nat(out, NAT(123)));
    uint32_t status = ssz_is_zero(schema, default_value, &arena, &verdict, NULL);
    CHECK(status == SSZ_OK && verdict == 1); /* optional error */
    /* Registration survived failures and subsequent suffix allocations. */
    uint8_t uninitialized_output[32];
    size_t written;
    OK(ssz_serialize(schema, value, uninitialized_output, sizeof(uninitialized_output),
        &arena, &written, &error));
    CHECK(written == 32 && uninitialized_output[0] == 1);
    CHECK(filled(uninitialized_output + 1, 31, 0));
    OK(ssz_hash_tree_root(schema, default_value, &arena, root, &error));
    CHECK(equal(BYTES(root), BYTES(zero)));
    return 0;
}

static int offsets_and_object_semantics(void) {
    static const ssz_json_field boolean[] = {{TEXT("kind"), STRING("Boolean")}};
    static const ssz_json_field bytes[] = {
        {TEXT("kind"), STRING("ByteList")}, {TEXT("limit"), NUMBER("8")}
    };
    static const ssz_json_field flag[] = {
        {TEXT("name"), STRING("flag")}, {TEXT("type"), OBJECT(boolean)}
    };
    static const ssz_json_field payload[] = {
        {TEXT("name"), STRING("payload")}, {TEXT("type"), OBJECT(bytes)}
    };
    static const ssz_json fields[] = {OBJECT(flag), OBJECT(payload)};
    static const ssz_json_field declaration[] = {
        {TEXT("kind"), STRING("Container")}, {TEXT("fields"), ARRAY(fields)}
    };
    static const ssz_json schema_json = OBJECT(declaration);
    static const ssz_json_field duplicate_fields[] = {
        {TEXT("flag"), {.tag=SSZ_JSON_BOOL,.boolean=0}},
        {TEXT("payload"), STRING("0xaabb")},
        {TEXT("flag"), {.tag=SSZ_JSON_BOOL,.boolean=1}}
    };
    static const ssz_json duplicate = OBJECT(duplicate_fields);
    static const uint8_t expected[] = {1,5,0,0,0,0xaa,0xbb};
    static const uint8_t invalid[] = {1,4,0,0,0,0xaa,0xbb};
    static const ssz_json_field unknown_fields[] = {
        {TEXT("zzz"), {.tag=SSZ_JSON_NULL}}, {TEXT("aaa"), {.tag=SSZ_JSON_NULL}}
    };
    static const ssz_json unknown = OBJECT(unknown_fields);
    static const ssz_json missing = {.tag=SSZ_JSON_OBJECT};
    ssz_bytes first_name = TEXT("aaa"), missing_name = TEXT("flag");
    const ssz_schema *schema = NULL;
    const ssz_value *value = NULL, *unchanged;
    reset_arena();
    OK(ssz_schema_from_json(&schema_json, &arena, &schema, &error));
    OK(ssz_value_from_json(schema, &duplicate, &arena, &value, &error));
    if (encoded(schema, value, BYTES(expected))) return 1;
    unchanged = value;
    EXPECT(ssz_deserialize(schema, BYTES(invalid), &arena, &unchanged, &error), SSZ_FIRST_OFFSET);
    CHECK(unchanged == value && same_nat(error.args[0], NAT(5)) && same_nat(error.args[1], NAT(4)));
    EXPECT(ssz_value_from_json(schema, &unknown, &arena, &unchanged, &error), SSZ_UNDECLARED_FIELD);
    CHECK(unchanged == value && equal(error.text, first_name)); /* sorted extra names */
    EXPECT(ssz_value_from_json(schema, &missing, &arena, &unchanged, &error), SSZ_MISSING_FIELD);
    CHECK(unchanged == value && equal(error.text, missing_name)); /* declared field order */
    return 0;
}

static int runtime_operations(void) {
    uint8_t bytes[10] = {0,1,2,3,4,5,6,7,8,9};
    static const uint8_t right[] = {0,1,0,1,2,3,4,5,6,7};
    static const uint8_t left[] = {0,1,2,3,4,5,6,7,6,7};
    CHECK(memmove(bytes+2, bytes, 8) == bytes+2 && equal(BYTES(bytes), BYTES(right)));
    CHECK(memmove(bytes, bytes+2, 8) == bytes && equal(BYTES(bytes), BYTES(left)));
    CHECK(memmove(bytes, bytes, sizeof(bytes)) == bytes && equal(BYTES(bytes), BYTES(left)));
    CHECK(memcpy(bytes, right, sizeof(bytes)) == bytes && equal(BYTES(bytes), BYTES(right)));
    CHECK(memcmp((uint8_t[]){0x80}, (uint8_t[]){0x7f}, 1) > 0);
    CHECK(memcmp((uint8_t[]){0}, (uint8_t[]){255}, 1) < 0);
    CHECK(memset(bytes, 0x123, sizeof(bytes)) == bytes && filled(bytes, sizeof(bytes), 0x23));
    CHECK(memcmp(NULL, NULL, 0) == 0);
    return 0;
}

int smoke_main(void) {
    case_name = "freestanding memory operations";
    if (runtime_operations()) return 1;
    case_name = "published SHA answers and raw operand widths";
    if (hash_answers()) return 1;
    case_name = "independent Merkle answers and >64-bit metadata";
    if (merkle_and_wide_metadata()) return 1;
    case_name = "scratch ownership, invalid inputs, defaults and compatibility";
    if (resources_and_defaults()) return 1;
    case_name = "offset payloads and JSON object semantics";
    if (offsets_and_object_semantics()) return 1;
    for (size_t i = 0; i < COUNT(fixtures); ++i) {
        case_name = fixtures[i].name;
        if (fixture(&fixtures[i])) return 1;
    }
    text("C caller: "); decimal(COUNT(fixtures));
    text(" pinned fixtures and direct ABI edge checks passed\n");
    return 0;
}
