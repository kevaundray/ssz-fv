import SszArm.MeasureBitsLimit

namespace SszArm.Measure.Bits.Limit

open Result
open Delimited (MemoryFrame)
open UintCodec (widthLoad)

macro "measure_bits_limit_expand" : tactic => `(tactic|
  (simp (config := {decide := true, instances := true}) only
    [result, suffix, headerResult, reservedResult, initial, state_simp_rules];
   measure_result_expand))

theorem result_frame (s : ArmState) (base : BitVec 64) (space : ErrorSpace s) :
    MemoryFrame (errorWrites s) s (result s base) := by
  rcases space with ⟨stack, bound, fields⟩
  intro address outside
  have slot := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [errorWrites])
  have payload := outside ((r (.GPR 19#5) s).toNat, 68) (by simp [errorWrites])
  measure_bits_limit_expand
  simp (disch := measure_result_side) [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem result_at (s : ArmState) (base : BitVec 64) (space : ErrorSpace s)
    (expected actual : SszNative.NatOperand)
    (expectedPointer : r (.GPR 22#5) s = expected.pointer)
    (expectedPayload : r (.GPR 23#5) s = expected.payload)
    (actualPointer : r (.GPR 21#5) s = actual.pointer)
    (actualPayload : r (.GPR 24#5) s = actual.payload)
    (expectedAt : expected.At (widthLoad s)) (actualAt : actual.At (widthLoad s))
    (expectedOwned : NatDivision.OperandOwned (errorWrites s) expected)
    (actualOwned : NatDivision.OperandOwned (errorWrites s) actual) :
    ResultAt (widthLoad (result s base)) (r (.GPR 19#5) s).toNat
      (.error (.limit expected actual)) := by
  have frame := result_frame s base space
  have expectedFinal := NatDivision.operand_at_preserved frame expected expectedAt expectedOwned
  have actualFinal := NatDivision.operand_at_preserved frame actual actualAt actualOwned
  rcases space with ⟨stack, bound, fields⟩
  change ErrorAt _ _ (.limit expected actual)
  refine ⟨?_, ?_, ⟨?_, ?_, expectedFinal⟩, ⟨?_, ?_, actualFinal⟩, ?_, ?_, ?_⟩
  all_goals
    simp only [errorOperands, errorCode, widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    measure_bits_limit_expand
    measure_result_reads
  all_goals simp only [expectedPointer, expectedPayload, actualPointer, actualPayload]

end SszArm.Measure.Bits.Limit
