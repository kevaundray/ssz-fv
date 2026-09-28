import SszX86.DispatchIntervals

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

def OperandOwned (s : MachineData) (address capacity used : BitVec 64) : NatOperand → Prop
  | .small _ => True
  | .large p words => ReadOnly s address capacity used p.toNat (8 * words.length)

theorem bitVector_owned (s : MachineData) (base : Int64) (ra : BitVec 64)
    (length : NatOperand) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s base .bitVector ra data address capacity used)
    (repr : NatArithmetic.operandAt (widthLoad s.dmem) (s.regs.rsi.toNat + 8) length)
    (borrowed : OperandOwned s address capacity used length) :
    SszX86.BitVector.Owned (bodyState s base .bitVector) (saved s ra)
      length data address capacity used := by
  have sp := body_spNat s base .bitVector h.stack_low
  refine {
    output_bound := by simpa only [body_output] using h.output_bound
    output_mapped := by simpa only [body_memory, body_output] using saved_mapped s _ _ h.output_mapped
    stack_low := by rw [sp]; have := h.stack_low; omega
    stack_bound := by rw [sp]; have := h.stack_low; have := h.stack_bound; omega
    work_mapped := ?_
    saved_at := h.saved_at
    output_work := ?_
    output_saved := ?_
    descriptor := ?_
    descriptor_owned := by simpa only [body_descriptor,
      show (if Kind.bitVector = Kind.progressiveBitList then 32 else 24) = 24 by decide] using
      h.descriptor_owned.bitVector (base := base) (kind := .bitVector) h.stack_low
    operand_owned := ?_
    data_length := by simpa only [body_length] using h.length
    source := by simpa only [body_memory, body_source] using h.source_view
    source_owned := by simpa only [body_source] using
      h.source_owned.bitVector (base := base) (kind := .bitVector) h.stack_low
    header_bound := by simpa only [body_arena] using h.header_bound
    address_load := ?_
    capacity_load := by simpa only [body_memory, body_arena,
      show (8 : BitVec 64) = 8#64 by decide] using
      (h.header_load 8 (by decide)).trans h.capacity_load
    used_load := by simpa only [body_memory, body_arena,
      show (16 : BitVec 64) = 16#64 by decide] using
      (h.header_load 16 (by decide)).trans h.used_load
    arena_bound := h.arena_bound
    used_bound := h.used_bound
    arena_nonzero := h.arena_nonzero
    arena_mapped := by simpa only [body_memory] using saved_mapped s _ _ h.arena_mapped
    arena_output := by simpa only [body_output] using h.arena_output
    arena_work := ?_
    arena_saved := ?_
    arena_header := by simpa only [body_arena] using h.arena_header
    header_output := by simpa only [body_arena, body_output] using h.header_output
    header_work := ?_
    cursor_saved := ?_ }
  · rw [body_memory, body_sp]
    have hm := h.stack_mapping 40 296 (by decide)
    have addr : s.regs.rsp.toBitVec - 472 + BitVec.ofNat 64 40 =
        s.regs.rsp.toBitVec - 360 - 72 := by bv_omega
    rw [addr] at hm
    exact hm
  · simpa only [SszX86.BitVector.workStart, SszX86.BitVector.workSize,
      Nat.add_zero, body_output] using
      body_interval s base .bitVector h.stack_low _ _ h.output_stack 72 0 296 (by decide) (by decide)
  · simpa only [Nat.sub_zero, body_output] using
      body_interval s base .bitVector h.stack_low _ _ h.output_stack 0 312 56 (by decide) (by decide)
  · refine ⟨?_, ?_, ?_⟩
    all_goals simp only [body_memory, body_descriptor]
    · rw [(h.descriptor_owned.subrange 8 8 (by decide)).width h.stack_low]
      exact repr.1
    · change widthLoad (savedMem s) (s.regs.rsi.toNat + 8 + 8) 8 = _
      rw [show s.regs.rsi.toNat + 8 + 8 = s.regs.rsi.toNat + 16 by omega,
        (h.descriptor_owned.subrange 16 8 (by decide)).width h.stack_low]
      exact repr.2.1
    · cases length with
      | small limb => trivial
      | large p words =>
        rcases repr.2.2 with ⟨positive, aligned, bound, bytes⟩
        refine ⟨positive, aligned, bound, ?_⟩
        intro i
        rw [(borrowed.subrange (8 * i.val) 8 (by have := i.isLt; omega)).width h.stack_low]
        exact bytes i
  · cases length with
    | small limb => trivial
    | large p words => exact borrowed.bitVector (base := base) (kind := .bitVector) h.stack_low
  · have loaded := h.header_load 0 (by decide)
    simpa only [body_memory, body_arena, BitVec.add_zero, h.address_load] using loaded
  · simpa only [SszX86.BitVector.workStart, SszX86.BitVector.workSize, Nat.add_zero] using
      body_interval s base .bitVector h.stack_low _ _ h.arena_stack 72 0 296 (by decide) (by decide)
  · simpa only [Nat.sub_zero] using
      body_interval s base .bitVector h.stack_low _ _ h.arena_stack 0 312 56 (by decide) (by decide)
  · simpa only [SszX86.BitVector.workStart, SszX86.BitVector.workSize,
      Nat.add_zero, body_arena] using
      body_interval s base .bitVector h.stack_low _ _ h.header_stack 72 0 296 (by decide) (by decide)
  · simpa only [Nat.sub_zero, body_arena] using
      body_interval s base .bitVector h.stack_low _ _ (apart_left h.header_stack 16 8 (by decide))
        0 312 56 (by decide) (by decide)

end SszX86.Dispatch
