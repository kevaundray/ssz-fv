import SszArm.CodecDecodeBoundedErrorFinish

namespace SszArm.Codec.Decode.Bounded

open SszNative
open UintCodec (widthLoad)
open Delimited (Protected)

structure ErrorInputs (s : ArmState) (cap actual : NatOperand) : Prop where
  capPointer : r (.GPR 21#5) s = cap.pointer
  capPayload : r (.GPR 22#5) s = cap.payload
  capAt : cap.At (widthLoad s)
  actualAt : ActualAt s (r (.GPR 20#5) s) actual
  actualBound : (r (.GPR 20#5) s).toNat + 16 ≤ 2 ^ 64
  actualRecord : Protected (errorWrites s) (r (.GPR 20#5) s).toNat 16
  capWords : NatDivision.OperandOwned (errorWrites s) cap
  actualWords : NatDivision.OperandOwned (errorWrites s) actual

/-- The final error carries the original cap and actual representations,
including borrowed padded/empty limbs, with no padding-byte assertion. -/
theorem error_image (s : ArmState) (base : BitVec 64) (cap actual : NatOperand)
    (space : ErrorSpace s) (inputs : ErrorInputs s cap actual) :
    SszArm.Codec.Measure.ErrorAt (widthLoad (errorState s base)) (r (.GPR 19#5) s).toNat
      (.primitive (.limit cap actual)) := by
  let a := ErrorStage.expected.result s base
  let b := ErrorStage.tag.result a base
  let c := ErrorStage.actual.result b base
  have aSpace := space.stage .expected base
  have bSpace := aSpace.stage .tag base
  have outA : r (.GPR 19#5) a = r (.GPR 19#5) s := error_stage_output .expected s base
  have outB : r (.GPR 19#5) b = r (.GPR 19#5) s :=
    (error_stage_output .tag a base).trans outA
  have aEight : r (.GPR 8#5) a = 1#64 := by
    simp [a, ErrorStage.result, ErrorStage.ops, block, Op.effect, put, next, state_simp_rules]
  have expected := expected_pair s base (by have := space.output; omega)
  have tag := tag_fields a base aSpace
  simp only [outA, aEight] at tag
  have fields := actual_fields b base bSpace
  simp only [outB] at fields
  have af := error_stage_frame .expected s base space.stack space.output
  have bf : Delimited.MemoryFrame (errorWrites s) a b := by
    simpa only [a, error_stage_writes] using error_stage_frame .tag a base aSpace.stack aSpace.output
  have before := af.trans bf
  have actualPointer : read_mem_bytes 8 (r (.GPR 20#5) b) b = actual.pointer := by
    have load := record_read before (r (.GPR 20#5) s) 16 0 8 inputs.actualBound
      inputs.actualRecord (by decide)
    simp only [BitVec.ofNat_zero, BitVec.add_zero] at load
    simpa only [b, a, error_stage_actual] using load.trans inputs.actualAt.1
  have actualPayload : read_mem_bytes 8 (r (.GPR 20#5) b + 8#64) b = actual.payload := by
    have load := record_read before (r (.GPR 20#5) s) 16 8 8 inputs.actualBound
      inputs.actualRecord (by decide)
    simpa only [b, a, error_stage_actual] using load.trans inputs.actualAt.2.1
  have h0 := actual_preserves_prefix b base bSpace 0 8 (by decide)
  have h8 := actual_preserves_prefix b base bSpace 8 8 (by decide)
  have h16 := actual_preserves_prefix b base bSpace 16 8 (by decide)
  have h24 := actual_preserves_prefix b base bSpace 24 8 (by decide)
  simp only [outB, BitVec.ofNat_zero, BitVec.add_zero] at h0 h8 h16 h24
  have cap0 := tag_preserves_expected a base aSpace 16 8 (by decide) (by decide)
  have cap8 := tag_preserves_expected a base aSpace 24 8 (by decide) (by decide)
  simp only [outA] at cap0 cap8
  have frame := error_state_frame s base space
  have capAt := NatDivision.operand_at_preserved frame cap inputs.capAt inputs.capWords
  have actualAt := NatDivision.operand_at_preserved frame actual inputs.actualAt.2.2 inputs.actualWords
  change _ ∧ _ ∧ (_ ∧ _ ∧ _) ∧ (_ ∧ _ ∧ _) ∧ _ ∧ _ ∧ _
  refine ⟨?_, ?_, ⟨?_, ?_, capAt⟩, ⟨?_, ?_, actualAt⟩, ?_, ?_, ?_⟩
  all_goals
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, Nat.add_assoc,
      errorState, state_simp_rules, restored]
  · exact congrArg (fun word : BitVec 64 => some word.toNat) (h0.trans tag.1)
  · exact congrArg (fun word : BitVec 64 => some word.toNat) (h8.trans tag.2)
  · exact congrArg (fun word : BitVec 64 => some word.toNat)
      (h16.trans (cap0.trans (expected.1.trans inputs.capPointer)))
  · exact congrArg (fun word : BitVec 64 => some word.toNat)
      (h24.trans (cap8.trans (expected.2.trans inputs.capPayload)))
  · exact congrArg (fun word : BitVec 64 => some word.toNat) (fields.1.trans actualPointer)
  · exact congrArg (fun word : BitVec 64 => some word.toNat) (fields.2.1.trans actualPayload)
  · exact congrArg (fun word : BitVec 64 => some word.toNat) fields.2.2.1
  · exact congrArg (fun word : BitVec 64 => some word.toNat) fields.2.2.2.1
  · exact congrArg (fun word : BitVec 32 => some word.toNat) fields.2.2.2.2

end SszArm.Codec.Decode.Bounded
