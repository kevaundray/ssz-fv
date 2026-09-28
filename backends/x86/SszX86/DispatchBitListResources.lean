import SszX86.DispatchIntervals

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

def listKind (tail : Bool) : Kind := if tail then .progressiveBitList else .bitList

theorem bitList_resources (s : MachineData) (base : Int64) (tail : Bool) (ra : BitVec 64)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s base (listKind tail) ra data address capacity used) :
    SszX86.BitList.Owned (bodyState s base (listKind tail)) (saved s ra)
      tail data address capacity used := by
  have sp := body_spNat s base (listKind tail) h.stack_low
  have descriptor : ReadOnly s address capacity used s.regs.rsi.toNat (if tail then 32 else 24) := by
    cases tail <;> simpa [listKind] using h.descriptor_owned
  have workRegion (p n : Nat) (apart : Body.Apart p n (stackStart s) 480) :
      Body.Apart p n (SszX86.BitList.workStart (bodyState s base (listKind tail)) tail)
        (SszX86.BitList.workBytes tail) := by
    cases tail
    · simpa only [SszX86.BitList.workStart, SszX86.BitList.workBytes,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using
        body_interval s base (listKind false) h.stack_low p n apart 112 0 152 (by decide) (by decide)
    · simpa only [SszX86.BitList.workStart, SszX86.BitList.workBytes,
        ↓reduceIte, Nat.sub_zero] using
        body_interval s base (listKind true) h.stack_low p n apart 0 256 104 (by decide) (by decide)
  refine {
    output_bound := h.output_bound
    output_mapped := saved_mapped s _ _ h.output_mapped
    stack_low := by intro _; rw [sp]; have := h.stack_low; omega
    stack_bound := by rw [sp]; have := h.stack_low; have := h.stack_bound; omega
    work_mapped := ?_
    saved := h.saved_at
    output_work := ?_
    output_saved := ?_
    length := h.length
    source := h.source_bytes
    source_owned := h.source_owned.bitList h.stack_low tail
    descriptor := descriptor.bitList h.stack_low tail
    header_bound := h.header_bound
    address_load := ?_
    capacity_load := (h.header_load 8 (by decide)).trans h.capacity_load
    used_load := (h.header_load 16 (by decide)).trans h.used_load
    arena_bound := h.arena_bound
    used_bound := h.used_bound
    arena_nonzero := h.arena_nonzero
    arena_mapped := saved_mapped s _ _ h.arena_mapped
    arena_output := h.arena_output
    arena_work := ?_
    arena_saved := ?_
    arena_header := h.arena_header
    header_output := h.header_output
    header_work := ?_
    cursor_saved := ?_ }
  · have low := h.stack_low
    have addr : BitVec.ofNat 64 (SszX86.BitList.workStart (bodyState s base (listKind tail)) tail) =
        s.regs.rsp.toBitVec - 472 + BitVec.ofNat 64 (if tail then 368 else 0) := by
      simp only [SszX86.BitList.workStart, sp]
      simp only [← UInt64.toNat_toBitVec] at low ⊢
      cases tail <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega
    rw [body_memory, addr]
    apply h.stack_mapping
    cases tail <;> decide
  · simpa only [body_output] using workRegion _ _ h.output_stack
  · simpa only [Nat.sub_zero, body_output] using
      body_interval s base (listKind tail) h.stack_low _ _ h.output_stack 0 312 56 (by decide) (by decide)
  · have loaded := h.header_load 0 (by decide)
    simpa only [body_memory, body_arena, BitVec.add_zero, h.address_load] using loaded
  · exact workRegion _ _ h.arena_stack
  · simpa only [Nat.sub_zero] using
      body_interval s base (listKind tail) h.stack_low _ _ h.arena_stack 0 312 56 (by decide) (by decide)
  · simpa only [body_arena] using workRegion _ _ h.header_stack
  · simpa only [Nat.sub_zero, body_arena] using
      body_interval s base (listKind tail) h.stack_low _ _
        (apart_left h.header_stack 16 8 (by decide)) 0 312 56 (by decide) (by decide)

end SszX86.Dispatch
