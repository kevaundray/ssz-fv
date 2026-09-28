import SszX86.DispatchIntervals

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

theorem uint_owned (s : MachineData) (base : Int64) (ra : BitVec 64)
    (expectedWidth : Nat) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s base .uint ra data address capacity used)
    (repr : NatOwned s address capacity used (s.regs.rsi.toNat + 8) expectedWidth)
    (physical : data.size < 2^63) :
    Body.Owned (bodyState s base .uint) (saved s ra) expectedWidth data address capacity used := by
  refine {
    tail := h.tail
    width_bound := by exact h.descriptor_owned.bound
    width_at := repr.represented h.stack_low
    length := h.length
    size := physical
    source := h.source_bytes
    source_owned := by simpa only [body_source] using
      h.source_owned.uint (base := base) (kind := .uint) h.stack_low
    descriptor := by simpa only [body_descriptor,
      show (if Kind.uint = Kind.progressiveBitList then 32 else 24) = 24 by decide] using
      h.descriptor_owned.uint (base := base) (kind := .uint) h.stack_low
    borrowed := ?_
    header := ?_
    arena_bound := h.arena_bound
    used_bound := h.used_bound
    arena_nonzero := h.arena_nonzero
    arena_mapped := by simpa only [body_memory] using saved_mapped s _ _ h.arena_mapped
    arena_output := by simpa only [body_output] using h.arena_output
    arena_stack := ?_
    arena_header := by simpa only [body_arena] using h.arena_header
    header_output := by simpa only [body_arena, body_output] using h.header_output
    header_stack := ?_ }
  · intro p words stored
    apply Or.inr
    apply (repr.large_protected h.stack_low p words ?_).uint (base := base) (kind := .uint) h.stack_low
    simpa only [body_memory, body_descriptor] using stored
  · refine ⟨by simpa only [body_arena, UInt64.toNat_toBitVec] using h.header_bound, ?_, ?_, ?_⟩
    · have loaded := h.header_load 0 (by decide)
      simpa only [body_memory, body_arena, BitVec.add_zero, h.address_load] using loaded
    · simpa only [body_memory, body_arena, show (8 : BitVec 64) = 8#64 by decide] using
        (h.header_load 8 (by decide)).trans h.capacity_load
    · simpa only [body_memory, body_arena, show (16 : BitVec 64) = 16#64 by decide] using
        (h.header_load 16 (by decide)).trans h.used_load
  · simpa only [Nat.sub_zero, Nat.add_zero] using
      body_interval s base .uint h.stack_low _ _ h.arena_stack 0 0 368 (by decide) (by decide)
  · simpa only [Nat.sub_zero, Nat.add_zero, body_arena] using
      body_interval s base .uint h.stack_low _ _ h.header_stack 0 0 368 (by decide) (by decide)

end SszX86.Dispatch
