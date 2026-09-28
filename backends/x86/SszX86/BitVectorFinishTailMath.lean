import SszX86.BitVectorMemory

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem finish_shift_zero (byte : UInt8) (remainder : BitVec 64)
    (bound : remainder.toNat < 8) :
    (byte.toBitVec >>> remainder.toNat = 0#8) ↔
      byte >>> UInt8.ofNat remainder.toNat = 0 := by
  rw [← UInt8.toNat_inj]
  rw [BitVec.toNat_eq]
  simp only [BitVec.toNat_ushiftRight, UInt8.toNat_toBitVec, BitVec.toNat_ofNat,
    UInt8.toNat_shiftRight, UInt8.toNat_ofNat_of_lt' (by change remainder.toNat < 256; omega),
    Nat.mod_eq_of_lt bound, UInt8.toNat_zero]

/-- The borrowed tail byte is physically read only in the nonempty branch. -/
theorem finish_tail_read (s u : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (owned : Owned {s with dmem := u.dmem} saved length data address capacity used)
    (size : u.regs.r14 = s.regs.r14) (positive : 0 < data.size) :
    Mem.loadInt u.dmem (s.regs.rdx.toBitVec + u.regs.r14.toBitVec - 1#64) 1 =
      some (data[data.size - 1]!.toNat : Int) := by
  have index : data.size - 1 < data.size := by omega
  have read := widthLoad_eq u.dmem (s.regs.rdx.toNat + (data.size - 1)) 1
    (data[data.size - 1]?.getD 0).toNat (owned.source _ index)
  have addressEq : BitVec.ofNat 64 (s.regs.rdx.toNat + (data.size - 1)) =
      s.regs.rdx.toBitVec + u.regs.r14.toBitVec - 1#64 := by
    rw [size, owned.data_length]
    have positiveBV : 0 < s.regs.r14.toBitVec.toNat := by
      simpa only [owned.data_length, UInt64.toNat_toBitVec] using positive
    change BitVec.ofNat 64 (s.regs.rdx.toBitVec.toNat + (s.regs.r14.toBitVec.toNat - 1)) = _
    bv_omega
  simpa only [addressEq, Array.getElem?_eq_getElem index, Option.getD_some,
    getElem!_pos data (data.size - 1) index] using read

/-- The shared result uses precisely the gate and byte test executed by the suffix. -/
theorem finish_result (length expected : NatOperand) (remainder : BitVec 64)
    (data : Ssz.Bytes) (physical : data.size < 2^64)
    (arithmetic : SszNative.BitVector.Expected length expected remainder)
    (checked : NatNarrow.runExact expected (BitVec.ofNat 64 data.size) = true) :
    SszNative.BitVector.finish length expected remainder data =
      if remainder = 0#64 ∨ data.size = 0 then .ok (BitVec.ofNat 128 length.value)
      else if data[data.size - 1]!.toBitVec >>> remainder.toNat = 0#8 then
        .ok (BitVec.ofNat 128 length.value) else .error .paddingBits := by
  obtain ⟨bound, narrow, scope⟩ := SszNative.BitVector.scope_narrows length expected remainder
    (BitVec.ofNat 64 data.size) arithmetic checked
  have wide : length.value < 2^128 := by omega
  have scopeValue : data.size = (length.value + 7) / 8 := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical, Nat.mod_eq_of_lt wide] using scope
  have built := SszNative.BitVector.construct_ok length data physical scopeValue
  have shift := finish_shift_zero data[data.size - 1]! remainder
    (SszNative.BitVector.expected_remainder_bound arithmetic)
  by_cases zero : remainder = 0#64
  · simp [SszNative.BitVector.finish, checked, zero, built]
  by_cases empty : data.size = 0
  · rw [SszNative.BitVector.finish, checked]
    simp [empty, built]
  have positive : 0 < data.size := by omega
  by_cases tailZero : data[data.size - 1]!.toBitVec >>> remainder.toNat = 0#8
  · simp [SszNative.BitVector.finish, checked, zero, empty, positive, built,
      tailZero, shift.mp tailZero]
  · have nonzero := mt shift.mpr tailZero
    simp [SszNative.BitVector.finish, checked, zero, empty, positive, tailZero, nonzero]

end SszX86.BitVector
