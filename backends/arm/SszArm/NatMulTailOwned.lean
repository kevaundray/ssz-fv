import SszArm.NatMulTailFrame

namespace SszArm.NatMul

open Delimited (Protected)

theorem TailFrame.header {s t : ArmState} {left right : SszNative.NatOperand}
    (frame : TailFrame s t) (owned : Owned s left right) (offset : Nat)
    (fits : offset + 8 ≤ 24) :
    read_mem_bytes 8 (r (.GPR 4#5) t + BitVec.ofNat 64 offset) t =
      read_mem_bytes 8 (r (.GPR 5#5) s + BitVec.ofNat 64 offset) s := by
  have space := (entry_local_covered s (outcome s left right)).protected owned.arenaLocal
  have address : (r (.GPR 5#5) s + BitVec.ofNat 64 offset).toNat =
      (r (.GPR 5#5) s).toNat + offset := by
    have bound := owned.arenaBound
    bv_omega
  rw [frame.arena]
  exact frame.memory.read _ 8 (by rw [address]; have bound := owned.arenaBound; omega)
    (by rw [address]; exact space.subspan offset 8 fits)

theorem TailFrame.arenaOf {s t : ArmState} {left right : SszNative.NatOperand}
    (frame : TailFrame s t) (owned : Owned s left right) :
    NatMulWord.arenaOf t = arenaOf s := by
  have base := frame.header owned 0 (by decide)
  have capacity := frame.header owned 8 (by decide)
  have used := frame.header owned 16 (by decide)
  simp only [BitVec.add_zero] at base
  unfold NatMulWord.arenaOf SszArm.NatMul.arenaOf NatAdd.arenaOf
  with_unfolding_all rw [base, capacity, used]

theorem TailFrame.operandAt {s t : ArmState} (frame : TailFrame s t)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand)
    (operand : SszNative.NatOperand) (input : operand.At (UintCodec.widthLoad s))
    (owned : NatAdd.OperandOwned (writesFor s result) operand) :
    operand.At (UintCodec.widthLoad t) :=
  NatAdd.operand_at_preserved ((entry_covered s result).frame frame.memory) operand input owned

theorem TailFrame.word_owned {s t : ArmState} {left right : SszNative.NatOperand}
    (frame : TailFrame s t) (owned : Owned s left right)
    (operand : SszNative.NatOperand) (factor : BitVec 64)
    (pointer : r (.GPR 1#5) t = operand.pointer)
    (payload : r (.GPR 2#5) t = operand.payload)
    (factorRegister : r (.GPR 3#5) t = factor)
    (input : operand.At (UintCodec.widthLoad s))
    (inputOwned : NatAdd.OperandOwned (writesFor s (outcome s left right)) operand)
    (model : outcome s left right = SszNative.NatMul.runWord operand factor
      (SszArm.NatMul.arenaOf s).base (SszArm.NatMul.arenaOf s).capacity (SszArm.NatMul.arenaOf s).used) :
    NatMulWord.Owned t operand factor := by
  have result : NatMulWord.outcome t operand factor = outcome s left right := by
    unfold NatMulWord.outcome
    rw [frame.arenaOf owned]
    exact model.symm
  refine ⟨pointer, payload, factorRegister,
    frame.operandAt (outcome s left right) operand input inputOwned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frame.output]; exact owned.outputBound
  · rw [frame.sp]; have bound := owned.stackBound; omega
  · have cover : BitVector.Covers [((r (.GPR 31#5) s).toNat - 144, 144)]
        [((r (.GPR 31#5) t).toNat - 48, 48)] := by
      intro span member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst span
      exact ⟨((r (.GPR 31#5) s).toNat - 144, 144), by simp,
        by rw [frame.sp]; omega, by rw [frame.sp]; omega⟩
    simpa only [frame.output] using cover.protected owned.outputStack
  · rw [frame.arena]; exact owned.arenaBound
  · rw [frame.arenaOf owned]; exact owned.arenaStorage
  · rw [frame.arenaOf owned]; exact owned.arenaNonnull
  · rw [result, frame.arena]
    exact (frame.local_covered (outcome s left right)).protected owned.arenaLocal
  · intro reservation allocated
    rw [result] at allocated ⊢
    have cover := covers_append_same (frame.local_covered (outcome s left right))
      [((r (.GPR 5#5) s).toNat, 24)]
    rw [frame.arena]
    exact cover.protected (owned.fresh reservation allocated)
  · rw [result]
    have cover := frame.writes_covered (outcome s left right)
    cases operand with
    | small word => trivial
    | large pointer words => exact cover.protected inputOwned

end SszArm.NatMul
