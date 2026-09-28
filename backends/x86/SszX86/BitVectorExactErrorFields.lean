import SszX86.BitVectorExactError

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- The copied final word preserves all 32 status bits and all 32 padding bits. -/
theorem exact_error_reason_padding (m : DataMem) (out : BitVec 64) (v : ExactErrorImage)
    (bound : out.toNat + 80 ≤ 2^64) :
    observe (exactErrorMem m out v) out 72 4 = some (v.w8.setWidth 32).toNat ∧
    observe (exactErrorMem m out v) out 76 4 = some (v.w8.extractLsb' 32 32).toNat := by
  have lowBytes : Int.ofBytes (((Int.toBytes 8 v.w8.toInt).drop 0).take 4) =
      v.w8.toInt.take 32 := ofBytes_toBytes 4 v.w8.toInt
  have highBytes : Int.ofBytes (((Int.toBytes 8 v.w8.toInt).drop 4).take 4) =
      (v.w8.toInt / 4294967296).take 32 := by
    change Int.ofBytes (Int.toBytes 4 (v.w8.toInt / 256 / 256 / 256 / 256)) = _
    rw [ofBytes_toBytes]
    have divisions : v.w8.toInt / 256 / 256 / 256 / 256 = v.w8.toInt / 4294967296 := by omega
    rw [divisions]
  have lowCast : (v.w8.toInt.take 32).toNat = (v.w8.setWidth 32).toNat := by
    simp only [Int.take, BitVec.toNat_setWidth, BitVec.toInt_eq_toNat_cond, Nat.reducePow,
      show (2 : Int)^32 = 4294967296 by decide]
    split <;> omega
  have highCast : ((v.w8.toInt / 4294967296).take 32).toNat =
      (v.w8.extractLsb' 32 32).toNat := by
    simp only [Int.take, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
      BitVec.toInt_eq_toNat_cond, Nat.reducePow,
      show (2 : Int)^32 = 4294967296 by decide]
    split <;> omega
  simpa only [lowBytes, highBytes, lowCast, highCast] using
    exact_error_status_padding m out v bound

/-- Restoring R11 does not undo its temporary slot write; all prologue saves remain intact. -/
theorem exact_error_saved_load (s : MachineData) (out : BitVec 64) (v : ExactErrorImage)
    (low : 72 ≤ s.regs.rsp.toBitVec.toNat)
    (outBound : out.toNat + 80 ≤ 2^64)
    (stackBound : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64)
    (apart : Body.Apart (s.regs.rsp.toBitVec.toNat + 312) 56 out.toNat 80)
    (off count : Nat) (lo : 312 ≤ off) (hi : off + count ≤ 368) :
    Mem.loadInt (exactErrorState s out v).dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count =
      Mem.loadInt s.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count := by
  apply memmove_loadInt_congr
  intro i hi'
  apply exact_error_frame
  · intro j hj
    unfold Body.Apart at apart
    bv_omega
  · intro j hj
    bv_omega

end SszX86.BitVector
