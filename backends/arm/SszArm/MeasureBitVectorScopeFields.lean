import SszArm.MeasureBitVectorScope

namespace SszArm.Measure.BitVector.Scope

open Result
open Delimited (MemoryFrame)
open UintCodec (widthLoad)

macro "measure_bitvector_scope_expand" : tactic => `(tactic|
  (simp (config := {decide := true, instances := true}) only
    [result, headerResult, headerMemory, headerSaved, fieldsResult, reservedResult,
     prefixResult, state_simp_rules];
   measure_result_expand))

theorem result_frame (s : ArmState) (base : BitVec 64) (space : ErrorSpace s) :
    MemoryFrame (errorWrites s) s (result s base) := by
  rcases space with ⟨stack, bound, fields⟩
  intro address outside
  have slot := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [errorWrites])
  have payload := outside ((r (.GPR 19#5) s).toNat, 68) (by simp [errorWrites])
  measure_bitvector_scope_expand
  simp (disch := measure_result_side) [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem]

theorem result_at (s : ArmState) (base : BitVec 64) (space : ErrorSpace s)
    (expected actual : SszNative.NatOperand)
    (expectedPointer : read_mem_bytes 8 (r (.GPR 1#5) s) s = expected.pointer)
    (expectedPayload : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = expected.payload)
    (actualPointer : r (.GPR 10#5) s = actual.pointer)
    (actualPayload : r (.GPR 8#5) s = actual.payload)
    (expectedAt : expected.At (widthLoad s)) (actualAt : actual.At (widthLoad s))
    (expectedOwned : NatDivision.OperandOwned (errorWrites s) expected)
    (actualOwned : NatDivision.OperandOwned (errorWrites s) actual) :
    ResultAt (widthLoad (result s base)) (r (.GPR 19#5) s).toNat
      (.error (.scope expected actual)) := by
  have frame := result_frame s base space
  have expectedFinal := NatDivision.operand_at_preserved frame expected expectedAt expectedOwned
  have actualFinal := NatDivision.operand_at_preserved frame actual actualAt actualOwned
  rcases space with ⟨stack, bound, fields⟩
  change ErrorAt _ _ (.scope expected actual)
  refine ⟨?_, ?_, ⟨?_, ?_, expectedFinal⟩, ⟨?_, ?_, actualFinal⟩, ?_, ?_, ?_⟩
  all_goals simp only [errorOperands, errorCode, widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
  all_goals measure_bitvector_scope_expand
  all_goals measure_result_reads
  all_goals simp only [expectedPointer, expectedPayload, actualPointer, actualPayload]
  all_goals rfl

@[simp] theorem result_program (s : ArmState) (base : BitVec 64) :
    (result s base).program = s.program := by
  simp [result, headerResult, headerMemory, headerSaved, fieldsResult, reservedResult,
    prefixResult, state_simp_rules]

@[simp] theorem result_error (s : ArmState) (base : BitVec 64) :
    read_err (result s base) = read_err s := by
  have headerError : ∀ u, read_err (headerResult u base) = read_err u := by
    intro u
    simp [headerResult, headerMemory, headerSaved, state_simp_rules]
  have fieldsError : ∀ u, read_err (fieldsResult u base) = read_err u := by
    intro u
    simp [fieldsResult, state_simp_rules]
  have reservedError : ∀ u, read_err (reservedResult u base) = read_err u := by
    intro u
    unfold reservedResult
    change r .ERR (w .PC (base + 3472#64) (Lower.wrongReserved.result u base)) = r .ERR u
    exact (r_of_w_different (by decide)).trans (Lower.error .wrongReserved u base)
  unfold result
  rw [status_error, headerError, fieldsError, reservedError]
  simp [prefixResult, state_simp_rules]

@[simp] theorem result_pc (s : ArmState) (base : BitVec 64) :
    read_pc (result s base) = base + 4116#64 := by
  unfold result
  exact status_pc _ base

@[simp] theorem result_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (result s base) = r (.GPR 31#5) s := by
  simp (config := {decide := true})
    [result, headerResult, headerMemory, headerSaved, fieldsResult, reservedResult,
     prefixResult, state_simp_rules]

@[simp] theorem result_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (result s base) = r (.SFP reg) s := by
  simp [result, headerResult, headerMemory, headerSaved, fieldsResult, reservedResult,
    prefixResult, state_simp_rules]

theorem result_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (eight : reg ≠ 8#5) (nine : reg ≠ 9#5) (ten : reg ≠ 10#5) (eleven : reg ≠ 11#5) :
    r (.GPR reg) (result s base) = r (.GPR reg) s := by
  simp [result, headerResult, headerMemory, headerSaved, fieldsResult, reservedResult,
    prefixResult, Lower.register, Lower.tmp, eight, nine, ten, eleven,
    NatExact.r_gpr_w, state_simp_rules]

end SszArm.Measure.BitVector.Scope
