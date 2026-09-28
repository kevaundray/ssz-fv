import SszX86.EmitBoolStores

namespace SszX86.Emit
open BoolCodec UintCodec SszNative.Serialize

theorem bool_written_post (s : MachineData) (value : Bool)
    (apart : Large.Disjoint s.regs.r14.toBitVec s.regs.rbx.toBitVec 1 8) :
    BodyPost s (emit .bool (.bool value)) (boolWritten s value) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl⟩
  · have address : BitVec.ofNat 64 s.regs.rbx.toNat = s.regs.rbx.toBitVec := by
      change BitVec.ofNat 64 s.regs.rbx.toBitVec.toNat = s.regs.rbx.toBitVec
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [boolWritten, widthLoad, address]
    rw [load_store_same _ _ 8 _ (by decide)]
    cases value <;> rfl
  · intro i hi
    have zero : i = 0 := by
      change i < 1 at hi
      omega
    subst i
    simp only [boolWritten, Mem.storeInt,
      show BitVec.ofNat 64 0 = (0 : BitVec 64) by decide]
    rw [memmove_store_lookup_outside]
    · have stored := memmove_store_lookup_inside s.dmem s.regs.r14.toBitVec
        (Int.toBytes 1 (if value then 1 else 0)) 0
        (by rw [Int.toBytes_length]; decide) (by rw [Int.toBytes_length]; decide)
      cases value
      · change (Mem.storeBytes s.dmem s.regs.r14.toBitVec (Int.toBytes 1 0)).get?
          (s.regs.r14.toBitVec + BitVec.ofNat 64 0) = some (0 : UInt8)
        exact stored.trans (show (Int.toBytes 1 0)[0]? = some (0 : UInt8) by decide)
      · change (Mem.storeBytes s.dmem s.regs.r14.toBitVec (Int.toBytes 1 1)).get?
          (s.regs.r14.toBitVec + BitVec.ofNat 64 0) = some (1 : UInt8)
        exact stored.trans (show (Int.toBytes 1 1)[0]? = some (1 : UInt8) by decide)
    · intro j hj equal
      have hi : j < 8 := by simpa only [Int.toBytes_length] using hj
      apply apart 0 (by decide) j hi
      simpa only [show BitVec.ofNat 64 0 = (0 : BitVec 64) by decide, BitVec.add_zero] using equal
  · intro a outside
    change (Mem.storeInt
      (Mem.storeInt s.dmem s.regs.r14.toBitVec 1 (if value then 1 else 0))
      s.regs.rbx.toBitVec 8 1).get? a = s.dmem.get? a
    unfold Mem.storeInt
    rw [memmove_store_lookup_outside]
    · apply memmove_store_lookup_outside
      intro i hi equal
      apply outside
      left
      refine ⟨i, ?_, equal⟩
      change i < 1
      simpa only [Int.toBytes_length] using hi
    · intro i hi equal
      exact outside (Or.inr (Or.inl ⟨i, by simpa only [Int.toBytes_length] using hi, equal⟩))

end SszX86.Emit
