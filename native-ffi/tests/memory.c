#include <stddef.h>
#include <stdint.h>
#include <limits.h>

void *memcpy(void *, const void *, size_t);
void *memmove(void *, const void *, size_t);
void *memset(void *, int, size_t);
int memcmp(const void *, const void *, size_t);
void smoke_write(const char *, size_t);

#define COUNT(a) (sizeof(a) / sizeof((a)[0]))
#define SAY(s) smoke_write((s), sizeof(s) - 1)
enum { BUFFER = 576 };
static unsigned char left[BUFFER], right[BUFFER];
static const size_t lengths[] = {0,1,7,8,15,16,17,31,32,63,64,65,127,128,129,255,256,257};

static unsigned char pattern(size_t i, size_t seed) {
    return (unsigned char)(37 + 17*i + 3*seed);
}

#if defined(__x86_64__)
/* Read the callee's real RET slot, without reserving it as a separate source
 * allocation. Global and caller-stack destinations exercise both move directions. */
uintptr_t copy_return_slot(void *);
uintptr_t move_return_slot(void *);
int compare_return_slot(void);
__asm__(".text\n.type copy_return_slot,@function\ncopy_return_slot:\n"
        "push %rbx\nmov %rdi,%rbx\nlea -8(%rsp),%rsi\nmov $8,%edx\n"
        "call memcpy\n.Lcopy_return:\ncmp %rbx,%rax\njne .Lcopy_bad\n"
        "lea .Lcopy_return(%rip),%rax\npop %rbx\nret\n"
        ".Lcopy_bad:\nxor %eax,%eax\npop %rbx\nret\n"
        ".size copy_return_slot,.-copy_return_slot\n"
        ".type move_return_slot,@function\nmove_return_slot:\n"
        "push %rbx\nmov %rdi,%rbx\nlea -8(%rsp),%rsi\nmov $8,%edx\n"
        "call memmove\n.Lmove_return:\ncmp %rbx,%rax\njne .Lmove_bad\n"
        "lea .Lmove_return(%rip),%rax\npop %rbx\nret\n"
        ".Lmove_bad:\nxor %eax,%eax\npop %rbx\nret\n"
        ".size move_return_slot,.-move_return_slot\n"
        ".type compare_return_slot,@function\ncompare_return_slot:\n"
        "sub $8,%rsp\nlea .Lcompare_return(%rip),%rax\nmov %rax,(%rsp)\n"
        "mov %rsp,%rsi\nlea -8(%rsp),%rdi\nmov $8,%edx\n"
        "call memcmp\n.Lcompare_return:\nadd $8,%rsp\nret\n"
        ".size compare_return_slot,.-compare_return_slot\n");

static int return_slot(uintptr_t (*operation)(void *)) {
    unsigned char local[32];
    for (unsigned pass = 0; pass < 2; ++pass) {
        unsigned char *bytes = pass ? local : right;
        size_t size = pass ? sizeof(local) : sizeof(right);
        for (size_t i = 0; i < size; ++i) bytes[i] = 0xa5;
        uintptr_t address = operation(bytes);
        if (!address) return 1;
        for (size_t i = 0; i < size; ++i) {
            unsigned char expected = i < 8 ? (unsigned char)(address >> (8*i)) : 0xa5;
            if (bytes[i] != expected) return 2;
        }
    }
    return 0;
}
#endif

static int check_copy(void) {
    if (memcpy(NULL, NULL, 0) != NULL || memcpy(right, NULL, 0) != right) return 1;
    for (size_t in = 0; in < 16; ++in) for (size_t out = 0; out < 16; ++out)
        for (size_t n = 0; n <= 257; ++n) {
            for (size_t i = 0; i < BUFFER; ++i) { left[i] = pattern(i,n); right[i] = 0xa5; }
            if (memcpy(right+out, left+in, n) != right+out) return 2;
            for (size_t i = 0; i < BUFFER; ++i) {
                unsigned char expected = i >= out && i-out < n ? pattern(i-out+in,n) : 0xa5;
                if (right[i] != expected || left[i] != pattern(i,n)) return 3;
            }
        }
#if defined(__x86_64__)
    if (return_slot(copy_return_slot)) return 4;
    SAY("memcpy: readonly RET-slot source with global and stack destinations passed\n");
#endif
    SAY("memcpy: 66048 alignment/length cases, exact source/output frames and null empty copies passed\n");
    return 0;
}

static int check_fill(void) {
    static const int extra[] = {INT_MIN,INT_MAX,-1,-256,256,511};
    if (memset(NULL, -1, (0)) != NULL) return 1;
    for (unsigned b = 0; b < 256+COUNT(extra); ++b) for (size_t out = 0; out < 16; ++out)
        for (size_t k = 0; k < COUNT(lengths); ++k) {
            int value = b < 256 ? (int)b : extra[b-256];
            size_t n = lengths[k];
            for (size_t i = 0; i < BUFFER; ++i) right[i] = 0xa5;
            if (memset(right+out, value, n) != right+out) return 2;
            for (size_t i = 0; i < BUFFER; ++i) {
                unsigned char expected = i >= out && i-out < n ? (unsigned char)value : 0xa5;
                if (right[i] != expected) return 3;
            }
        }
    SAY("memset: 75456 byte-value/alignment/boundary cases, exact frames and null empty fill passed\n");
    return 0;
}

static int check_move(void) {
    static const int shifts[] = {
        -128,-127,-65,-64,-33,-32,-31,-30,-29,-28,-27,-26,-25,-24,-23,-22,-21,-20,
        -19,-18,-17,-16,-15,-14,-13,-12,-11,-10,-9,-8,-7,-6,-5,-4,-3,-2,-1,
        0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,
        25,26,27,28,29,30,31,32,33,64,65,127,128
    };
    if (memmove(NULL, NULL, 0) != NULL || memmove(right, NULL, 0) != right) return 1;
    for (size_t align = 0; align < 16; ++align) for (size_t d = 0; d < COUNT(shifts); ++d)
        for (size_t n = 0; n <= 257; ++n) {
            size_t in = 128+align, out = (size_t)((ptrdiff_t)in+shifts[d]);
            for (size_t i = 0; i < BUFFER; ++i) left[i] = pattern(i,n);
            if (memmove(left+out, left+in, n) != left+out) return 2;
            for (size_t i = 0; i < BUFFER; ++i) {
                unsigned char expected = i >= out && i-out < n ? pattern(i-out+in,n) : pattern(i,n);
                if (left[i] != expected) return 3;
            }
        }
#if defined(__x86_64__)
    if (return_slot(move_return_slot)) return 4;
    SAY("memmove: readonly RET-slot source with global and stack destinations passed\n");
#endif
    SAY("memmove: 309600 overlapping/disjoint/self-copy cases, original-source snapshots and exact frames passed\n");
    return 0;
}

/* Volatile reads keep the independent reference from becoming a memcmp call. */
static int reference_compare(const volatile unsigned char *a,
                             const volatile unsigned char *b, size_t n) {
    for (size_t i = 0; i < n; ++i) {
        unsigned char x = a[i], y = b[i];
        if (x != y) return (int)x-(int)y;
    }
    return 0;
}

static int order(int value) { return (value > 0) - (value < 0); }

static int check_compare(void) {
    if (memcmp(NULL, NULL, 0) != 0) return 1;
    for (size_t i = 0; i < BUFFER; ++i) { left[i] = 0xa5; right[i] = 0x5a; }
    for (unsigned a = 0; a < 256; ++a) for (unsigned b = 0; b < 256; ++b) {
        left[0] = (unsigned char)a; right[0] = (unsigned char)b;
        if (order(memcmp(left, right, 1)) != order((int)a-(int)b)) return 2;
        if (left[0] != a || right[0] != b) return 3;
    }
    for (size_t i = 1; i < BUFFER; ++i) if (left[i] != 0xa5 || right[i] != 0x5a) return 3;

    for (size_t in = 0; in < 16; ++in) for (size_t out = 0; out < 16; ++out)
        for (size_t k = 0; k < COUNT(lengths); ++k) {
            size_t n = lengths[k];
            for (size_t i = 0; i < BUFFER; ++i) {
                left[i] = pattern(i,n); right[i] = pattern(i+in+1024-out,n);
            }
            if (n) left[in+n-1] = right[out+n-1] = 128;
            if (memcmp(left+in, right+out, n) != 0) return 4;
            for (size_t pos = 0; pos < n; ++pos) {
                unsigned char old = right[out+pos];
                unsigned char different = (unsigned char)(old^0x80);
                right[out+pos] = different;
                int expected = (int)old-(int)different;
                /* A later mismatch has the opposite order: first difference wins. */
                unsigned char last = expected > 0 ? 255 : 0;
                if (pos+1 < n) right[out+n-1] = last;
                if (order(memcmp(left+in, right+out, n)) != order(expected) ||
                    order(memcmp(right+out, left+in, n)) != -order(expected)) return 5;
                /* Check fields before restoring them; all other bytes are checked
                 * against the original image after the mismatch-position sweep. */
                if (left[in+pos] != old || right[out+pos] != different ||
                    left[in+n-1] != 128 || right[out+n-1] != (pos+1 < n ? last : different)) return 6;
                right[out+pos] = old;
                right[out+n-1] = 128;
            }
            for (size_t i = 0; i < BUFFER; ++i) {
                unsigned char a = n && i == in+n-1 ? 128 : pattern(i,n);
                unsigned char b = n && i == out+n-1 ? 128 : pattern(i+in+1024-out,n);
                if (left[i] != a || right[i] != b) return 7;
            }
        }
    for (size_t in = 0; in < 32; ++in) for (size_t out = 0; out < 32; ++out)
        for (size_t k = 0; k < COUNT(lengths); ++k) {
            size_t n = lengths[k];
            for (size_t i = 0; i < BUFFER; ++i) left[i] = pattern(i,n);
            int expected = reference_compare(left+in, left+out, n);
            if (order(memcmp(left+in, left+out, n)) != order(expected)) return 8;
            for (size_t i = 0; i < BUFFER; ++i) if (left[i] != pattern(i,n)) return 9;
        }
#if defined(__x86_64__)
    if (compare_return_slot() != 0) return 10;
    SAY("memcmp: readonly RET-slot input passed\n");
#endif
    SAY("memcmp: all 65536 byte pairs, every first-difference position, unsigned ordering and overlapping readonly views passed\n");
    return 0;
}

int smoke_main(void) {
    int result = check_copy();
    if (result) return 16+result;
    result = check_fill();
    if (result) return 32+result;
    result = check_move();
    if (result) return 48+result;
    result = check_compare();
    return result ? 64+result : 0;
}
