import SszArm.CodecDecodeBoundedEntry
import SszArm.CodecDecodeBoundedContract
import SszArm.MeasureHelpersCompareOwned

namespace SszArm.Codec.Decode.Bounded

open SszNative
open UintCodec (widthLoad)

@[simp] theorem prepared_program (s : ArmState) (base : BitVec 64) :
    (prepared s base).program = s.program := by simp [prepared, state_simp_rules]

@[simp] theorem prepared_memory (s : ArmState) (base : BitVec 64) :
    (prepared s base).mem = s.mem := by simp [prepared, state_simp_rules]

@[simp] theorem prepared_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (prepared s base) = r (.GPR 31#5) s := by
  simp [prepared, state_simp_rules]

@[simp] theorem prepared_observe (s : ArmState) (base : BitVec 64) :
    widthLoad (prepared s base) = widthLoad s := by
  funext address bytes
  simp [widthLoad, prepared, state_simp_rules]

/-- The actual BL reaches the immutable Nat.compare provider. Its arbitrary
raw operands are reconstructed from the records loaded by these six linked
instructions; no abstract comparison result is assumed. -/
theorem comparison_run (s : ArmState) (base : BitVec 64) (cap actual : NatOperand)
    (code : JointCodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 32#64)
    (capAt : LimitAt s (r (.GPR 1#5) s) (some cap))
    (actualAt : ActualAt s (r (.GPR 2#5) s) actual)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (capOwned : NatDivision.OperandOwned (SszArm.Measure.Helpers.loweringWrites s) cap)
    (actualOwned : NatDivision.OperandOwned (SszArm.Measure.Helpers.loweringWrites s) actual) :
    ∃ fuel t, run (6 + fuel) s = t ∧ NatCompare.Frame (prepared s base) t ∧
      read_pc t = base + 56#64 ∧ read_err t = .None ∧
      (r (.GPR 0#5) t).setWidth 8 = NatABI.orderingByte (compare actual.value cap.value) := by
  obtain ⟨tag, capPointer, capPayload, capWords⟩ := capAt
  obtain ⟨actualPointer, actualPayload, actualWords⟩ := actualAt
  let c := prepared s base
  have executed : run 6 s = c := call_run s base code.body error aligned pc
  have cCode : NatCompare.CodeAt c (base - 78128#64) := by
    simpa only [c, NatCompare.CodeAt, prepared_program] using code.compare
  have cError : read_err c = .None := by simpa [c, prepared, state_simp_rules] using error
  have cAligned : CheckSPAlignment c :=
    CheckSPAlignment_of_r_sp_aligned (prepared_sp s base) (BoolCodec.stack_aligned s aligned)
  have cPC : read_pc c = base - 78128#64 + BitVec.ofNat 64 NatCompare.entry := by
    simp [c, prepared, NatCompare.entry, state_simp_rules]
  have left : NatMemory.Pair (widthLoad c) (r (.GPR 0#5) c) (r (.GPR 1#5) c) actual.value := by
    simpa [c, prepared, state_simp_rules, actualPointer, actualPayload]
      using NatOperand.At.pair (widthLoad s) actual actualWords
  have right : NatMemory.Pair (widthLoad c) (r (.GPR 2#5) c) (r (.GPR 3#5) c) cap.value := by
    simpa [c, prepared, state_simp_rules, capPointer, capPayload]
      using NatOperand.At.pair (widthLoad s) cap capWords
  have leftOwned : NatCompare.Owned c (r (.GPR 0#5) c) (r (.GPR 1#5) c) := by
    simpa [c, prepared, NatCompare.Owned, state_simp_rules, actualPointer, actualPayload]
      using SszArm.Measure.Helpers.compare_operand_owned s actual stack actualWords actualOwned
  have rightOwned : NatCompare.Owned c (r (.GPR 2#5) c) (r (.GPR 3#5) c) := by
    simpa [c, prepared, NatCompare.Owned, state_simp_rules, capPointer, capPayload]
      using SszArm.Measure.Helpers.compare_operand_owned s cap stack capWords capOwned
  obtain ⟨fuel, t, runCompare, frame, returned, noError, _, _, order, _, _⟩ :=
    NatCompare.compare_correct c (base - 78128#64) actual.value cap.value cCode cError cAligned
      cPC left right leftOwned rightOwned
  refine ⟨fuel, t, ?_, frame, ?_, noError, order⟩
  · rw [run_plus, executed, runCompare]
  · simpa [c, prepared, state_simp_rules] using returned

end SszArm.Codec.Decode.Bounded
