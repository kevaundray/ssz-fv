import SszArm.MeasureResultScope
import SszArm.MeasureResultLimit
import SszArm.MeasureResultFields

namespace SszArm.Measure.Result

open Delimited (MemoryFrame)
open UintCodec (widthLoad)

macro "measure_semantic_writer_expand" : tactic => `(tactic|
  (simp only [scopeResult, scopePrefix, scopePrepared, limitResult, limitPrefix, limitPrepared] <;>
   measure_result_expand))

theorem scope_frame (s : ArmState) (base : BitVec 64) (space : ErrorSpace s) :
    MemoryFrame (errorWrites s) s (scopeResult s base) := by
  rcases space with ⟨stack, bound, fields⟩
  intro address outside
  have slot := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [errorWrites])
  have payload := outside ((r (.GPR 19#5) s).toNat, 68) (by simp [errorWrites])
  measure_semantic_writer_expand
  simp (disch := measure_result_side) [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem limit_frame (s : ArmState) (base : BitVec 64) (space : ErrorSpace s) :
    MemoryFrame (errorWrites s) s (limitResult s base) := by
  rcases space with ⟨stack, bound, fields⟩
  intro address outside
  have slot := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [errorWrites])
  have payload := outside ((r (.GPR 19#5) s).toNat, 68) (by simp [errorWrites])
  measure_semantic_writer_expand
  simp (disch := measure_result_side) [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem scope_at (s : ArmState) (base : BitVec 64) (space : ErrorSpace s)
    (expected : SszNative.NatOperand)
    (pointer : r (.GPR 8#5) s = expected.pointer)
    (payload : r (.GPR 9#5) s = expected.payload)
    (input : expected.At (widthLoad s))
    (owned : NatDivision.OperandOwned (errorWrites s) expected) :
    ResultAt (widthLoad (scopeResult s base)) (r (.GPR 19#5) s).toNat
      (.error (.scope expected (.small (r (.GPR 20#5) s)))) := by
  have preserved := NatDivision.operand_at_preserved (scope_frame s base space) expected input owned
  rcases space with ⟨stack, bound, fields⟩
  change ErrorAt _ _ (.scope expected (.small (r (.GPR 20#5) s)))
  refine ⟨?_, ?_, ⟨?_, ?_, preserved⟩, ⟨?_, ?_, trivial⟩, ?_, ?_, ?_⟩
  all_goals simp only [errorOperands, errorCode, SszNative.NatOperand.pointer,
    SszNative.NatOperand.payload, widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
  all_goals measure_semantic_writer_expand
  all_goals measure_result_reads
  all_goals simp only [pointer, payload]
  all_goals rfl

theorem limit_at (s : ArmState) (base : BitVec 64) (space : ErrorSpace s)
    (expected : SszNative.NatOperand)
    (pointer : r (.GPR 8#5) s = expected.pointer)
    (payload : r (.GPR 9#5) s = expected.payload)
    (input : expected.At (widthLoad s))
    (owned : NatDivision.OperandOwned (errorWrites s) expected) :
    ResultAt (widthLoad (limitResult s base)) (r (.GPR 19#5) s).toNat
      (.error (.limit expected (.small (r (.GPR 20#5) s)))) := by
  have preserved := NatDivision.operand_at_preserved (limit_frame s base space) expected input owned
  rcases space with ⟨stack, bound, fields⟩
  change ErrorAt _ _ (.limit expected (.small (r (.GPR 20#5) s)))
  refine ⟨?_, ?_, ⟨?_, ?_, preserved⟩, ⟨?_, ?_, trivial⟩, ?_, ?_, ?_⟩
  all_goals simp only [errorOperands, errorCode, SszNative.NatOperand.pointer,
    SszNative.NatOperand.payload, widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
  all_goals measure_semantic_writer_expand
  all_goals measure_result_reads
  all_goals simp only [pointer, payload]
  all_goals rfl

end SszArm.Measure.Result
