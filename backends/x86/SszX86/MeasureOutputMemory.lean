import SszX86.MeasureOutputCore
import SszX86.NatAddOutputMemory

namespace SszX86.Measure
open SszNative UintCodec BoolCodec

private theorem observe_same (m : DataMem) (out : BitVec 64)
    (off byteCount : Nat) (value : Int) (hb : byteCount ≤ 2^64) :
    BoolCodec.observe (Mem.storeInt m (out + BitVec.ofNat 64 off) byteCount value) out off byteCount =
      some (value.take (8 * byteCount)).toNat := by
  rw [BoolCodec.observe, load_store_same m _ byteCount value hb]
  rfl

private theorem observe_disjoint (m : DataMem) (out : BitVec 64)
    (a n b k : Nat) (value : Int)
    (ha : a + n ≤ 72) (hb : b + k ≤ 72) (hs : a + n ≤ b ∨ b + k ≤ a) :
    BoolCodec.observe (Mem.storeInt m (out + BitVec.ofNat 64 b) k value) out a n =
      BoolCodec.observe m out a n := by
  unfold BoolCodec.observe
  rw [load_store_disjoint _ _ _ _ _ _ (by
    intro i hi j hj
    bv_omega)]

private theorem load_observe (m : DataMem) (out : BitVec 64) (off byteCount : Nat) :
    widthLoad m (out.toNat + off) byteCount = BoolCodec.observe m out off byteCount := by
  simp only [widthLoad, BoolCodec.observe, width_address]

private theorem load_observe_zero (m : DataMem) (out : BitVec 64) (byteCount : Nat) :
    widthLoad m out.toNat byteCount = BoolCodec.observe m out 0 byteCount := by
  simp only [widthLoad, BoolCodec.observe, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero]

private theorem signed64_nat (value : BitVec 64) :
    (value.toInt.take 64).toNat = value.toNat := by
  have h := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := value))
  simp only [BitVec.toNat_ofInt] at h
  simpa [Int.take] using h

macro "measure_result_reads" : tactic => `(tactic|
  (simp (disch := first | assumption | omega | decide) only
     [planMem, wrongTypeMem, scalarErrorMem, load_observe, load_observe_zero,
      observe_disjoint, BoolCodec.observe_store64, observe_same,
      Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, signed64_nat]
   try decide))

theorem plan_fields (m : DataMem) (out pointer payload : BitVec 64) :
    widthLoad (planMem m out pointer payload) out.toNat 8 = some 8 ∧
    widthLoad (planMem m out pointer payload) (out.toNat + 8) 8 = some 0 ∧
    widthLoad (planMem m out pointer payload) (out.toNat + 16) 8 = some pointer.toNat ∧
    widthLoad (planMem m out pointer payload) (out.toNat + 24) 8 = some payload.toNat ∧
    widthLoad (planMem m out pointer payload) (out.toNat + 32) 8 = some 0 ∧
    widthLoad (planMem m out pointer payload) (out.toNat + 64) 4 = some 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> measure_result_reads

theorem plan_reads (m : DataMem) (out : BitVec 64) (operand : NatOperand)
    (owned : operand.At (widthLoad (planMem m out operand.pointer operand.payload))) :
    PlanAt (widthLoad (planMem m out operand.pointer operand.payload)) out.toNat operand := by
  obtain ⟨children, childCount, pointer, payload, leading, status⟩ :=
    plan_fields m out operand.pointer operand.payload
  exact ⟨children, childCount, ⟨pointer, payload, owned⟩, leading, status⟩

theorem wrong_type_reads (m : DataMem) (out : BitVec 64) :
    ErrorAt (widthLoad (wrongTypeMem m out)) out.toNat .wrongType := by
  change SemanticErrorAt (widthLoad (wrongTypeMem m out)) out.toNat 1 (.small 0) (.small 0)
  unfold SemanticErrorAt NatArithmetic.operandAt
  refine ⟨?_, ?_, ⟨?_, ?_, trivial⟩, ⟨?_, ?_, trivial⟩, ?_, ?_, ?_⟩ <;> measure_result_reads

theorem scalar_error_reads (m : DataMem) (out : BitVec 64) (code : Nat)
    (expected : NatOperand) (actual : BitVec 64) (codeCases : code = 2 ∨ code = 3)
    (owned : expected.At (widthLoad
      (scalarErrorMem m out code expected.pointer expected.payload actual))) :
    SemanticErrorAt (widthLoad (scalarErrorMem m out code expected.pointer expected.payload actual))
      out.toNat code expected (.small actual) := by
  unfold SemanticErrorAt NatArithmetic.operandAt
  refine ⟨?_, ?_, ⟨?_, ?_, owned⟩, ⟨?_, ?_, trivial⟩, ?_, ?_, ?_⟩
  all_goals rcases codeCases with rfl | rfl <;> measure_result_reads
  all_goals rfl

/-- Success padding40..63 and68 onward is not writable. -/
theorem plan_frame (m : DataMem) (out pointer payload : BitVec 64) :
    MemoryFrame m (planMem m out pointer payload)
      (fun a => InSpan a out 40 ∨ InSpan a (out + 64) 4) := by
  intro a outside
  have lower : ∀ i < 40, a ≠ out + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside (Or.inl ⟨i, hi, equal⟩)
  have status : ∀ i < 4, a ≠ out + BitVec.ofNat 64 64 + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside (Or.inr ⟨i, hi, equal⟩)
  have removeStatus (memory : DataMem) :
      (Mem.storeInt memory (out + BitVec.ofNat 64 64) 4 0).get? a = memory.get? a := by
    apply memmove_store_lookup_outside
    intro i hi
    exact status i (by simpa only [Int.toBytes_length] using hi)
  dsimp only [planMem]
  rw [removeStatus]
  simp (disch := first | assumption | omega | decide) only [BoolCodec.store_frame (limit := 40)]

theorem wrong_type_frame (m : DataMem) (out : BitVec 64) :
    MemoryFrame m (wrongTypeMem m out) (fun a => InSpan a out 68) := by
  intro a outside
  have apart : ∀ i < 68, a ≠ out + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  simp (disch := first | assumption | omega | decide) only
    [wrongTypeMem, BoolCodec.store_frame (limit := 68)]

theorem scalar_error_frame (m : DataMem) (out : BitVec 64) (code : Nat)
    (expectedPointer expectedPayload actualPayload : BitVec 64) :
    MemoryFrame m (scalarErrorMem m out code expectedPointer expectedPayload actualPayload)
      (fun a => InSpan a out 68) := by
  intro a outside
  have apart : ∀ i < 68, a ≠ out + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  simp (disch := first | assumption | omega | decide) only
    [scalarErrorMem, BoolCodec.store_frame (limit := 68)]

end SszX86.Measure
