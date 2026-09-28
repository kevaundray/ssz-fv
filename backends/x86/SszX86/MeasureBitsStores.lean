import SszX86.MeasureBitsMemory

namespace SszX86.Measure.Bits
open UintCodec

/-- This swaps only disjoint actual stores. It is used for the native list's
interleaving of local spills with its committed arena cursor. -/
theorem store_commute (m : DataMem) (p q : BitVec 64) (n k : Nat) (v w : Int)
    (pn : n ≤ 2^64) (qk : k ≤ 2^64) (apart : Large.Disjoint p q n k) :
    Mem.storeInt (Mem.storeInt m p n v) q k w =
      Mem.storeInt (Mem.storeInt m q k w) p n v := by
  apply Std.ExtHashMap.ext_getElem?
  intro a
  change (Mem.storeInt (Mem.storeInt m p n v) q k w).get? a =
    (Mem.storeInt (Mem.storeInt m q k w) p n v).get? a
  by_cases inP : InSpan a p n
  · obtain ⟨i, hi, rfl⟩ := inP
    have outsideQ : ∀ j < k, p + BitVec.ofNat 64 i ≠ q + BitVec.ofNat 64 j := apart i hi
    rw [show (Mem.storeInt (Mem.storeInt m p n v) q k w).get? (p + BitVec.ofNat 64 i) =
        (Mem.storeInt m p n v).get? (p + BitVec.ofNat 64 i) by
      apply memmove_store_lookup_outside
      simpa only [Int.toBytes_length] using outsideQ]
    simpa only [Mem.storeInt] using
      (memmove_store_lookup_inside m p (Int.toBytes n v) i (by simpa only [Int.toBytes_length] using hi)
        (by simpa only [Int.toBytes_length] using pn)).trans
        (memmove_store_lookup_inside (Mem.storeInt m q k w) p (Int.toBytes n v) i
          (by simpa only [Int.toBytes_length] using hi)
          (by simpa only [Int.toBytes_length] using pn)).symm
  · by_cases inQ : InSpan a q k
    · obtain ⟨j, hj, rfl⟩ := inQ
      have outsideP : ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i := by
        intro i hi equal
        exact inP ⟨i, hi, equal⟩
      rw [show (Mem.storeInt (Mem.storeInt m q k w) p n v).get? (q + BitVec.ofNat 64 j) =
          (Mem.storeInt m q k w).get? (q + BitVec.ofNat 64 j) by
        apply memmove_store_lookup_outside
        simpa only [Int.toBytes_length] using outsideP]
      simpa only [Mem.storeInt] using
        (memmove_store_lookup_inside (Mem.storeInt m p n v) q (Int.toBytes k w) j
          (by simpa only [Int.toBytes_length] using hj)
          (by simpa only [Int.toBytes_length] using qk)).trans
          (memmove_store_lookup_inside m q (Int.toBytes k w) j
            (by simpa only [Int.toBytes_length] using hj)
            (by simpa only [Int.toBytes_length] using qk)).symm
    · have outsideP : ∀ i < n, a ≠ p + BitVec.ofNat 64 i := by
        intro i hi equal
        exact inP ⟨i, hi, equal⟩
      have outsideQ : ∀ j < k, a ≠ q + BitVec.ofNat 64 j := by
        intro j hj equal
        exact inQ ⟨j, hj, equal⟩
      simp only [Mem.storeInt]
      rw [memmove_store_lookup_outside _ q a _ (by simpa only [Int.toBytes_length] using outsideQ)]
      rw [memmove_store_lookup_outside _ p a _ (by simpa only [Int.toBytes_length] using outsideP)]
      rw [memmove_store_lookup_outside _ p a _ (by simpa only [Int.toBytes_length] using outsideP)]
      rw [memmove_store_lookup_outside _ q a _ (by simpa only [Int.toBytes_length] using outsideQ)]

end SszX86.Measure.Bits
