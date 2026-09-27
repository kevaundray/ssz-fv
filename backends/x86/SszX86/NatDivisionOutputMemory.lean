import SszX86.NatDivisionOutput

namespace SszX86.NatDivision
open UintCodec
open BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private theorem result_observe_same (m : DataMem) (out : BitVec 64)
    (off byteCount : Nat) (value : Int) (hb : byteCount ≤ 2^64) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 off) byteCount value) out off byteCount =
      some (value.take (8 * byteCount)).toNat := by
  rw [observe, load_store_same m _ byteCount value hb]
  rfl

private theorem result_observe_disjoint (m : DataMem) (out : BitVec 64)
    (a n b k : Nat) (value : Int)
    (ha : a + n ≤ 68) (hb : b + k ≤ 68) (hs : a + n ≤ b ∨ b + k ≤ a) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 b) k value) out a n =
      observe m out a n := by
  unfold observe
  rw [load_store_disjoint _ _ _ _ _ _ (by
    intro i hi j hj
    bv_omega)]

private theorem result_load_observe (m : DataMem) (out : BitVec 64) (off byteCount : Nat) :
    widthLoad m (out.toNat + off) byteCount = observe m out off byteCount := by
  simp only [widthLoad, observe, width_address]

private theorem result_load_observe_zero (m : DataMem) (out : BitVec 64) (byteCount : Nat) :
    widthLoad m out.toNat byteCount = observe m out 0 byteCount := by
  simp only [widthLoad, observe, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero]

private theorem result_signed64_nat (value : BitVec 64) :
    (value.toInt.take 64).toNat = value.toNat := by
  have h := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := value))
  simp only [BitVec.toNat_ofInt] at h
  simpa [Int.take] using h

macro "natdiv_result_reads" : tactic => `(tactic|
  (simp (disch := first | assumption | omega | decide) only
     [resultSuccessMem, resultPairMem, resultErrorMem,
      result_load_observe, result_load_observe_zero, result_observe_disjoint,
      observe_store64, result_observe_same, Nat.reduceAdd, Nat.reduceMul, result_signed64_nat]
   try decide))

theorem result_success_reads (m : DataMem) (out pointer payload remainder : BitVec 64) :
    widthLoad (resultSuccessMem m out pointer payload remainder) out.toNat 8 = some pointer.toNat ∧
      widthLoad (resultSuccessMem m out pointer payload remainder) (out.toNat + 8) 8 = some payload.toNat ∧
      widthLoad (resultSuccessMem m out pointer payload remainder) (out.toNat + 16) 8 = some remainder.toNat ∧
      widthLoad (resultSuccessMem m out pointer payload remainder) (out.toNat + 64) 4 = some 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> natdiv_result_reads

theorem result_error_observed (m : DataMem) (out : BitVec 64) :
    SszNative.NatArithmetic.DivisionResultAt (widthLoad (resultErrorMem m out)) out.toNat
      (.error .scratchExhausted) := by
  unfold SszNative.NatArithmetic.DivisionResultAt SszNative.NatArithmetic.errorAt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> natdiv_result_reads

theorem result_success_observed (m : DataMem) (out remainder : BitVec 64)
    (quotient : SszNative.NatOperand)
    (stored : quotient.At (widthLoad
      (resultSuccessMem m out quotient.pointer quotient.payload remainder))) :
    SszNative.NatArithmetic.DivisionResultAt
      (widthLoad (resultSuccessMem m out quotient.pointer quotient.payload remainder))
      out.toNat (.ok (quotient, remainder)) := by
  obtain ⟨pointer, payload, rem, reason⟩ :=
    result_success_reads m out quotient.pointer quotient.payload remainder
  exact ⟨⟨pointer, payload, stored⟩, rem, reason⟩

/-- Publication only modifies the exact private result object, not the whole
allocation and not just the quotient's normalized visible prefix. -/
theorem result_success_mem_frame (m : DataMem) (out pointer payload remainder address : BitVec 64)
    (ha : ∀ i < 68, address ≠ out + BitVec.ofNat 64 i) :
    (resultSuccessMem m out pointer payload remainder).get? address = m.get? address := by
  simp (disch := first | assumption | omega | decide) only
    [resultSuccessMem, resultPairMem, store_frame (limit := 68)]

theorem result_error_mem_frame (m : DataMem) (out address : BitVec 64)
    (ha : ∀ i < 68, address ≠ out + BitVec.ofNat 64 i) :
    (resultErrorMem m out).get? address = m.get? address := by
  simp (disch := first | assumption | omega | decide) only
    [resultErrorMem, store_frame (limit := 68)]

end SszX86.NatDivision
