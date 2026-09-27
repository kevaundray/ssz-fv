/* Independent Python-generated full-width answers plus native word division.
 * No C 128-bit division is used as an oracle: that would call the kernel again. */
#include <stddef.h>
#include <stdint.h>

typedef unsigned __int128 Wide;
typedef struct {
    uint64_t a_lo, a_hi, d_lo, d_hi, q_lo, q_hi;
} DivisionCase;
#include "division-vectors.h"

extern Wide __udivti3(Wide, Wide);
extern void smoke_write(const char *, size_t);
static Wide (*volatile divide_kernel)(Wide, Wide) = __udivti3;
#define SAY(s) smoke_write((s), sizeof(s)-1)

static Wide wide(uint64_t lo, uint64_t hi) {
    return (Wide)lo | ((Wide)hi << 64);
}

static void hex(Wide value) {
    const char digits[] = "0123456789abcdef";
    char text[32];
    for (unsigned i = 0; i < 32; ++i) {
        text[31-i] = digits[(unsigned)value & 15];
        value >>= 4;
    }
    smoke_write(text, sizeof(text));
}

int smoke_main(void) {
    for (uint64_t a = 0; a < 256; ++a) {
        for (uint64_t d = 1; d < 256; ++d) {
            if (divide_kernel(a, d) != a/d) {
                SAY("word division mismatch\n");
                return 1;
            }
        }
    }
    for (size_t i = 0; i < sizeof(cases)/sizeof(cases[0]); ++i) {
        const DivisionCase *c = &cases[i];
        Wide a = wide(c->a_lo, c->a_hi), d = wide(c->d_lo, c->d_hi);
        Wide expected = wide(c->q_lo, c->q_hi), actual = divide_kernel(a, d);
        if (actual != expected) {
            SAY("division mismatch: "); hex(a); SAY(" / "); hex(d);
            SAY(" expected "); hex(expected); SAY(" actual "); hex(actual);
            SAY("\n");
            return 2;
        }
    }
    SAY("division: 65280 word cases and all Python full-width answers passed\n");
    return 0;
}
