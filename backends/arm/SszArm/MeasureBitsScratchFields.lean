import SszArm.MeasureBitsScratch

namespace SszArm.Measure.Bits.Scratch

open Result
open Delimited (MemoryFrame)
open UintCodec (widthLoad)

macro "measure_bits_scratch_expand" : tactic => `(tactic|
  (simp (config := {decide := true, instances := true}) only
    [finalResult, expectedResult, actualResult, statusReady,
      headerResult, reservedResult, initialResult, state_simp_rules];
   measure_result_expand))

theorem final_frame (s : ArmState) (base : BitVec 64) (space : ErrorSpace s) :
    MemoryFrame (errorWrites s) s (finalResult s base) := by
  rcases space with ⟨stack, bound, fields⟩
  intro address outside
  have slot := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [errorWrites])
  have payload := outside ((r (.GPR 19#5) s).toNat, 68) (by simp [errorWrites])
  measure_bits_scratch_expand
  simp (disch := measure_result_side) [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem final_at (s : ArmState) (base : BitVec 64) (space : ErrorSpace s) :
    ResultAt (widthLoad (finalResult s base)) (r (.GPR 19#5) s).toNat
      (.error (.arithmetic .scratchExhausted)) := by
  rcases space with ⟨stack, bound, fields⟩
  change ErrorAt _ _ (.arithmetic .scratchExhausted)
  refine ⟨?_, ?_, ⟨?_, ?_, trivial⟩, ⟨?_, ?_, trivial⟩, ?_, ?_, ?_⟩
  all_goals
    simp only [errorOperands, errorCode, SszNative.NatOperand.pointer,
      SszNative.NatOperand.payload, widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    measure_bits_scratch_expand
    measure_result_reads

end SszArm.Measure.Bits.Scratch
