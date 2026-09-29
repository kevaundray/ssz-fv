import SszArm.SerializeFinishMeasure
import SszArm.CodecMeasureError

namespace SszArm.Codec.Serialize

open Delimited (MemoryFrame)
open UintCodec (widthLoad)
open SszNative.Codec (Error)

private theorem errorCode_nonzero (reason : Error) : Measure.errorCode reason ≠ 0 := by
  cases reason with
  | primitive reason =>
    cases reason with
    | arithmetic reason => cases reason <;> decide
    | wrongType | limit _ _ | scope _ _ | outputTooSmall =>
      simp [Measure.errorCode, SszArm.Measure.errorCode]
  | offsetOverflow _ | unknownSelector _ | scopeTooSmall _ _ | scopeUndivided _ _
  | scopeWidthless | firstOffset _ _ | offsetUnordered | offsetPastScope
  | offsetUnaligned | offsetBelowTable | truncated | notABit _ | paddingBits
  | emptyEncoding | noDelimiter | trailingZeros | noSelector =>
    simp [Measure.errorCode]

/-- A recursive native error determines the wrapper's real status branch.
This is derived from the returned active field, never an entry assumption. -/
theorem error_status {s : ArmState} {reason : Error}
    (stored : Measure.ErrorAt (widthLoad s)
      ((SszArm.Serialize.Finish.sp s).toNat + 24) reason) :
    read_mem_bytes 4 (SszArm.Serialize.Finish.sp s + 88#64) s ≠ 0#32 := by
  have observed := stored.2.2.2.2.2.2
  have status : (read_mem_bytes 4 (SszArm.Serialize.Finish.sp s + 88#64) s).toNat =
      Measure.errorCode reason := by
    simpa only [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, show 24#64 + 64#64 = 88#64 by decide, Option.some.injEq] using observed
  intro zero
  rw [zero] at status
  exact errorCode_nonzero reason status.symm

/-- The original PC52..132 error continuation copies the entire physical
72-byte return image. Only its active 68 bytes are interpreted as an error;
the copy does not initialize previously unspecified padding. -/
theorem error_return_correct (base : BitVec 64) (s : ArmState) (reason : Error)
    (code : SszArm.Serialize.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 52#64)
    (space : SszArm.Serialize.Finish.MeasureSpace s)
    (stored : Measure.ErrorAt (widthLoad s)
      ((SszArm.Serialize.Finish.sp s).toNat + 24) reason)
    (leftOwned : NatDivision.OperandOwned (SszArm.Serialize.Finish.measureWrites s)
      (Measure.errorOperands reason).1)
    (rightOwned : NatDivision.OperandOwned (SszArm.Serialize.Finish.measureWrites s)
      (Measure.errorOperands reason).2) :
    run 21 s = SszArm.Serialize.Finish.measureReturned base s ∧
      Measure.ErrorAt (widthLoad (SszArm.Serialize.Finish.measureReturned base s))
        (SszArm.Serialize.Finish.result s).toNat reason ∧
      MemoryFrame (SszArm.Serialize.Finish.measureWrites s)
        s (SszArm.Serialize.Finish.measureReturned base s) := by
  have frame := SszArm.Serialize.Finish.measure_return_frame base s space
  refine ⟨SszArm.Serialize.Finish.measure_return_run base s code error aligned pc
    (error_status stored), ?_, frame⟩
  apply Measure.ErrorAt.copy stored
  · intro offset width within
    unfold widthLoad
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat]
    simp only [BitVec.setWidth_eq]
    have sourceAddress :
        BitVec.ofNat 64 ((SszArm.Serialize.Finish.sp s).toNat + 24 + offset) =
          SszArm.Serialize.Finish.sp s + BitVec.ofNat 64 (24 + offset) := by
      simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]
    rw [sourceAddress, SszArm.Serialize.Finish.measure_return_read base s space offset width
      (by omega)]
  · exact NatDivision.operand_at_preserved frame _ stored.operands.1 leftOwned
  · exact NatDivision.operand_at_preserved frame _ stored.operands.2 rightOwned

end SszArm.Codec.Serialize
