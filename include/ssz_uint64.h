#ifndef SSZ_UINT64_H
#define SSZ_UINT64_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Low-level SSZ uint64 memory kernels, not length-checking codec entrypoints.
 * The pointer must identify eight accessible, non-wrapping bytes; alignment is
 * unrestricted. Store requires caller-owned writable bytes disjoint from code
 * and the active return slot. Load requires readable bytes.
 * Store changes only those eight bytes. Load leaves all memory unchanged.
 * The proofs cover Linux x86-64 System V and AArch64 AAPCS64 model execution;
 * real mapping/permissions and agreement of the ISA models with hardware remain
 * caller/platform obligations. See the backend proof module contracts.
 */
void ssz_store_u64(uint8_t *output, uint64_t value);
uint64_t ssz_load_u64(const uint8_t *input);

#ifdef __cplusplus
}
#endif

#endif
