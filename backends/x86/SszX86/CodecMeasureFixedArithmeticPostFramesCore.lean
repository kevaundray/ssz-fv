import SszX86.CodecMeasureFixedArithmeticOwnershipMemory

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

/-- Actual helper writes include its caller-owned temporary result and CALL slot
inside the root stack, initialized allocation payloads, and only a committed cursor. -/
def ArithmeticTraceWrites (original : MachineData) (bytes : Nat)
    (calls : List (NatArithmetic.Outcome NatOperand)) (a : BitVec 64) : Prop :=
  Codec.StackWrites original.regs.rsp.toBitVec bytes a ∨
    Measure.AllocationWrites calls a ∨
    (Measure.Allocated calls ∧ Codec.InSpan a (original.regs.rdx.toBitVec + 16) 8)

theorem arithmetic_outside_of_no_span (a : BitVec 64) (p n : Nat)
    (outside : ¬ Codec.InSpan a (BitVec.ofNat 64 p) n) : Body.Outside a.toNat p n := by
  by_contra inside
  have lower : p ≤ a.toNat := by unfold Body.Outside at inside; omega
  have upper : a.toNat < p + n := by unfold Body.Outside at inside; omega
  apply outside
  refine ⟨a.toNat - p, by omega, ?_⟩
  rw [← BitVec.ofNat_add, Nat.add_sub_of_le lower]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- This lifts a proved helper memory frame; it is not an execution assumption. -/
theorem arithmetic_frame_lift (original caller : MachineData) (base : Int64)
    (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (address capacity used originalRa ra : BitVec 64) (bytes helper : Nat)
    (owned : Owned original base r desc address capacity used originalRa bytes)
    (memory : caller.dmem = original.dmem)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (enough : 144 + helper ≤ bytes) (call : NatArithmetic.Outcome NatOperand)
    (after : DataMem)
    (frame : ∀ a : BitVec 64,
      Body.Outside a.toNat caller.regs.rsp.toNat 72 →
      Body.Outside a.toNat ((caller.regs.rsp.toBitVec - 8).toNat - helper) helper →
      (∀ reservation, call.allocation = some reservation →
        Body.Outside a.toNat (original.regs.rdx.toNat + 16) 8 ∧
        Body.Outside a.toNat reservation.pointer (8 * call.written.length)) →
      after.get? a = (arithmeticCallState caller ra).dmem.get? a) :
    Codec.MemoryFrame original.dmem after (ArithmeticTraceWrites original bytes [call]) := by
  have low := owned.stack.lowEnough
  have callerNat : caller.regs.rsp.toNat = original.regs.rsp.toNat - 136 := by
    simp only [← UInt64.toNat_toBitVec] at low ⊢
    rw [stack]
    bv_omega
  have pushedNat : (caller.regs.rsp.toBitVec - 8).toNat = original.regs.rsp.toNat - 144 := by
    simp only [← UInt64.toNat_toBitVec] at low ⊢
    rw [stack]
    bv_omega
  have rootPointer : BitVec.ofNat 64 (original.regs.rsp.toNat - bytes) =
      original.regs.rsp.toBitVec - BitVec.ofNat 64 bytes := by
    simp only [← UInt64.toNat_toBitVec] at low ⊢
    bv_omega
  intro a outside
  have rootOutside : Body.Outside a.toNat (original.regs.rsp.toNat - bytes) bytes := by
    apply arithmetic_outside_of_no_span
    rw [rootPointer]
    exact fun h => outside (Or.inl h)
  have second : after.get? a = (arithmeticCallState caller ra).dmem.get? a := by
    apply frame
    · rw [callerNat]
      unfold Body.Outside at *
      omega
    · rw [pushedNat]
      unfold Body.Outside at *
      omega
    · intro reservation allocated
      constructor
      · apply arithmetic_outside_of_no_span
        intro inside
        apply outside
        right; right
        refine ⟨⟨call, by simp, reservation, allocated⟩, ?_⟩
        simpa only [← UInt64.toNat_toBitVec, width_address] using inside
      · apply arithmetic_outside_of_no_span
        intro inside
        exact outside (Or.inr (Or.inl ⟨call, by simp, reservation, allocated, inside⟩))
  exact second.trans (arithmetic_call_frame original caller ra bytes memory stack (by omega) a
    (fun h => outside (Or.inl h)))

end SszX86.CodecMeasureFixed
