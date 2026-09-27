import SszX86.NatAddOutput

namespace SszX86.NatAdd
open UintCodec
open BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private theorem observe_same (m : DataMem) (out : BitVec 64)
    (off byteCount : Nat) (value : Int) (hb : byteCount ≤ 2^64) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 off) byteCount value) out off byteCount =
      some (value.take (8 * byteCount)).toNat := by
  rw [observe, load_store_same m _ byteCount value hb]
  rfl

private theorem observe_disjoint (m : DataMem) (out : BitVec 64)
    (a n b k : Nat) (value : Int)
    (ha : a + n ≤ 68) (hb : b + k ≤ 68) (hs : a + n ≤ b ∨ b + k ≤ a) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 b) k value) out a n =
      observe m out a n := by
  unfold observe
  rw [load_store_disjoint _ _ _ _ _ _ (by
    intro i hi j hj
    bv_omega)]

private theorem load_observe (m : DataMem) (out : BitVec 64) (off byteCount : Nat) :
    widthLoad m (out.toNat + off) byteCount = observe m out off byteCount := by
  simp only [widthLoad, observe, width_address]

private theorem load_observe_zero (m : DataMem) (out : BitVec 64) (byteCount : Nat) :
    widthLoad m out.toNat byteCount = observe m out 0 byteCount := by
  simp only [widthLoad, observe, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero]

private theorem signed64_nat (value : BitVec 64) :
    (value.toInt.take 64).toNat = value.toNat := by
  have h := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := value))
  simp only [BitVec.toNat_ofInt] at h
  simpa [Int.take] using h

macro "natadd_result_reads" : tactic => `(tactic|
  (simp (disch := first | assumption | omega | decide) only
     [successMem, pairMem, errorMem, countErrorMem,
      load_observe, load_observe_zero, observe_disjoint, observe_store64, observe_same,
      Nat.reduceAdd, Nat.reduceMul, signed64_nat]
   try decide))

/-- Success writes only the two native Nat fields and the four-byte status. -/
theorem success_reads (m : DataMem) (out pointer payload : BitVec 64) :
    widthLoad (successMem m out pointer payload) out.toNat 8 = some pointer.toNat ∧
      widthLoad (successMem m out pointer payload) (out.toNat + 8) 8 = some payload.toNat ∧
      widthLoad (successMem m out pointer payload) (out.toNat + 64) 4 = some 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> natadd_result_reads

theorem error_reads (m : DataMem) (out : BitVec 64) :
    SszNative.NatArithmetic.errorAt (widthLoad (errorMem m out)) out.toNat .scratchExhausted := by
  unfold SszNative.NatArithmetic.errorAt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> natadd_result_reads

theorem count_error_reads (m : DataMem) (out : BitVec 64) :
    SszNative.NatArithmetic.errorAt (widthLoad (countErrorMem m out)) out.toNat .scratchExhausted := by
  unfold SszNative.NatArithmetic.errorAt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> natadd_result_reads

theorem success_mem_frame (m : DataMem) (out pointer payload address : BitVec 64)
    (ha : ∀ i < 68, address ≠ out + BitVec.ofNat 64 i) :
    (successMem m out pointer payload).get? address = m.get? address := by
  simp (disch := first | assumption | omega | decide) only
    [successMem, pairMem, store_frame (limit := 68)]

theorem error_mem_frame (m : DataMem) (out address : BitVec 64)
    (ha : ∀ i < 68, address ≠ out + BitVec.ofNat 64 i) :
    (errorMem m out).get? address = m.get? address := by
  simp (disch := first | assumption | omega | decide) only
    [errorMem, store_frame (limit := 68)]

theorem count_error_mem_frame (m : DataMem) (out address : BitVec 64)
    (ha : ∀ i < 68, address ≠ out + BitVec.ofNat 64 i) :
    (countErrorMem m out).get? address = m.get? address := by
  simp (disch := first | assumption | omega | decide) only
    [countErrorMem, store_frame (limit := 68)]

end SszX86.NatAdd
