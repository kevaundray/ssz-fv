import SszArm.MeasureResultSuccess
import SszArm.MeasureResultWrong
import SszArm.UintResultMemory

namespace SszArm.Measure.Result

open Delimited (MemoryFrame Protected)
open UintCodec (widthLoad)

structure SuccessSpace (s : ArmState) : Prop where
  stack : 16 ≤ (r (.GPR 31#5) s).toNat
  bound : (r (.GPR 19#5) s).toNat + 68 ≤ 2^64
  fields : (r (.GPR 19#5) s).toNat + 40 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 19#5) s).toNat
  status : (r (.GPR 19#5) s).toNat + 68 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 19#5) s).toNat + 64

structure ErrorSpace (s : ArmState) : Prop where
  stack : 16 ≤ (r (.GPR 31#5) s).toNat
  bound : (r (.GPR 19#5) s).toNat + 68 ≤ 2^64
  fields : (r (.GPR 19#5) s).toNat + 68 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 19#5) s).toNat

def successWrites (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16), ((r (.GPR 19#5) s).toNat, 40),
    ((r (.GPR 19#5) s).toNat + 64, 4)]

def errorWrites (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16), ((r (.GPR 19#5) s).toNat, 68)]

macro "measure_result_side" : tactic => `(tactic|
  first | assumption | omega | bv_omega)

macro "measure_result_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [successResult, successPrefix, wrongResult, wrongPrefix, statusResult,
     Lower.result, Lower.memory, Lower.kind, Lower.offset, Lower.tmp, Lower.low,
     Lower.high, Lower.finish, Payload.store, savedPair,
     state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd])

macro "measure_result_reads" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    (disch := measure_result_side) only
    [state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.setWidth_ofNat_of_le,
     BitVec.sub_add_cancel, BitVec.add_sub_cancel, UintCodec.Tail.write_pair_words,
     BoolCodec.read_mem_bytes_write_mem_bytes_same,
     BoolCodec.read_mem_bytes_write_mem_bytes_disjoint])

theorem success_frame (s : ArmState) (base : BitVec 64) (space : SuccessSpace s) :
    MemoryFrame (successWrites s) s (successResult s base) := by
  rcases space with ⟨stack, bound, fields, status⟩
  intro address outside
  have slot := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [successWrites])
  have payload := outside ((r (.GPR 19#5) s).toNat, 40) (by simp [successWrites])
  have flag := outside ((r (.GPR 19#5) s).toNat + 64, 4) (by simp [successWrites])
  change address.toNat < (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat - 16 + 16 ≤ address.toNat at slot
  measure_result_expand
  simp (disch := measure_result_side) [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem wrong_frame (s : ArmState) (base : BitVec 64) (space : ErrorSpace s) :
    MemoryFrame (errorWrites s) s (wrongResult s base) := by
  rcases space with ⟨stack, bound, fields⟩
  intro address outside
  have slot := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [errorWrites])
  have payload := outside ((r (.GPR 19#5) s).toNat, 68) (by simp [errorWrites])
  measure_result_expand
  simp (disch := measure_result_side) [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem success_at (s : ArmState) (base : BitVec 64) (space : SuccessSpace s)
    (operand : SszNative.NatOperand)
    (pointer : r (.GPR 21#5) s = operand.pointer)
    (payload : r (.GPR 20#5) s = operand.payload)
    (input : operand.At (widthLoad s))
    (owned : NatDivision.OperandOwned (successWrites s) operand) :
    ResultAt (widthLoad (successResult s base)) (r (.GPR 19#5) s).toNat (.ok operand) := by
  have preserved := NatDivision.operand_at_preserved (success_frame s base space) operand input owned
  rcases space with ⟨stack, bound, fields, status⟩
  refine ⟨?_, ?_, ⟨?_, ?_, preserved⟩, ?_, ?_⟩
  all_goals simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
  all_goals measure_result_expand
  all_goals measure_result_reads
  all_goals simp only [pointer, payload]

theorem wrong_at (s : ArmState) (base : BitVec 64) (space : ErrorSpace s) :
    ResultAt (widthLoad (wrongResult s base)) (r (.GPR 19#5) s).toNat (.error .wrongType) := by
  rcases space with ⟨stack, bound, fields⟩
  change ErrorAt _ _ .wrongType
  refine ⟨?_, ?_, ⟨?_, ?_, trivial⟩, ⟨?_, ?_, trivial⟩, ?_, ?_, ?_⟩
  all_goals
    simp only [errorOperands, errorCode, SszNative.NatOperand.pointer,
      SszNative.NatOperand.payload, widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    measure_result_expand
    measure_result_reads

end SszArm.Measure.Result
