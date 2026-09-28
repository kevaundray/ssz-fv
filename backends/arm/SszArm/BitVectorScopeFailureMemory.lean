import SszArm.BitVectorCopySpace
import SszArm.BitVectorErrorExec
import SszArm.BitVectorStageState

namespace SszArm.BitVector.ScopeFailure

open UintCodec (widthLoad)
open Delimited (MemoryFrame Protected)

/-- The scope-error preparation changes only its three call arguments and PC. -/
theorem prepared_working {s c : ArmState} {length : SszNative.NatOperand}
    (current : Working s c length) (base : BitVec 64) :
    Working s (Stages.CallPreparation.scopeError.result c base) length := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa (config := {decide := true})
      [Stages.CallPreparation.result, state_simp_rules] using current.error
  · simpa (config := {decide := true})
      [Stages.CallPreparation.result, state_simp_rules] using current.sp
  · simpa (config := {decide := true})
      [Stages.CallPreparation.result, state_simp_rules] using current.output
  · simpa (config := {decide := true})
      [Stages.CallPreparation.result, state_simp_rules] using current.input
  · simpa (config := {decide := true})
      [Stages.CallPreparation.result, state_simp_rules] using current.size
  · simpa (config := {decide := true})
      [Stages.CallPreparation.result, state_simp_rules] using current.pointer
  · simpa (config := {decide := true})
      [Stages.CallPreparation.result, state_simp_rules] using current.payload
  · intro reg low high
    simpa (config := {decide := true})
      [Stages.CallPreparation.result, state_simp_rules] using current.vectors reg low high

/-- The final three instructions write exactly the eight-byte outer tag. -/
theorem tag_frame_exact (c : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 23#5) c).toNat + 8 ≤ 2^64) :
    MemoryFrame [((r (.GPR 23#5) c).toNat, 8)] c
      (ErrorTail.Tail.tag.result c base) := by
  have stored := Delimited.store_frame c (r (.GPR 23#5) c) 8 1#64 physical
  simpa only [MemoryFrame, ErrorTail.Tail.result, state_simp_rules,
    ArmState.mem_w_eq_mem] using stored

theorem tag_frame {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (output : r (.GPR 23#5) c = r (.GPR 0#5) s)
    (base : BitVec 64) :
    MemoryFrame (localWrites s) c (ErrorTail.Tail.tag.result c base) := by
  have bound := owned.outputBound
  have physical : (r (.GPR 23#5) c).toNat + 8 ≤ 2^64 := by rw [output]; omega
  have cover : Covers (localWrites s) [((r (.GPR 23#5) c).toNat, 8)] := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, output] using
      output_copy_covered owned 0 8 (by decide) (by decide)
  exact cover.frame (tag_frame_exact c base physical)

theorem tag_value (c : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 23#5) c).toNat + 8 ≤ 2^64) :
    widthLoad (ErrorTail.Tail.tag.result c base) (r (.GPR 23#5) c).toNat 8 = some 1 := by
  have loaded := BoolCodec.read_mem_bytes_write_mem_bytes_same
    c 8 (r (.GPR 23#5) c) 1#64 physical
  have one : (1#64).toNat = 1 := rfl
  simpa only [widthLoad, ErrorTail.Tail.result, state_simp_rules,
    BitVec.ofNat_toNat, BitVec.setWidth_eq, one] using
    congrArg (fun value : BitVec 64 => some value.toNat) loaded

/-- All 72 copied bytes survive tagging, including the native padding bytes. -/
theorem tag_copied (c : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 23#5) c).toNat + 80 ≤ 2^64)
    (offset bytes : Nat) (within : offset + bytes ≤ 72) :
    widthLoad (ErrorTail.Tail.tag.result c base)
        ((r (.GPR 23#5) c).toNat + 8 + offset) bytes =
      widthLoad c ((r (.GPR 23#5) c).toNat + 8 + offset) bytes := by
  apply (tag_frame_exact c base (by omega)).load _ _ (by omega)
  right
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  exact Or.inr (by omega)

end SszArm.BitVector.ScopeFailure
