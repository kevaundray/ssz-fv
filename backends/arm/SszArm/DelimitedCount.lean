import SszArm.DelimitedClz
import SszArm.DelimitedCountArithmetic
import SszArm.DelimitedZeroMemory
import SszArm.Udivti3Arithmetic

namespace SszArm.Delimited

open BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def countThreshold : BitVec 64 := 2305843009213693953#64

def countSlot (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (r (.GPR 10#5) s)
    (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) countThreshold s)

theorem clz_start_memory (s : ArmState) (base : BitVec 64) :
    (block base clzStartOps s).mem = (countSlot s).mem := by
  simp [block, clzStartOps, Op.effect, put, next, countSlot, countThreshold,
    state_simp_rules, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  apply mem_write_mem_bytes_of_mem_eq
  simp only [ArmState.mem_w_eq_mem]
  apply mem_write_mem_bytes_of_mem_eq
  simp [ArmState.mem_w_eq_mem]

theorem clz_start_saved (s : ArmState) (base : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    let t := block base clzStartOps s
    read_mem_bytes 8 (r (.GPR 31#5) t) t = countThreshold ∧
      read_mem_bytes 8 (r (.GPR 31#5) t + 8#64) t = r (.GPR 10#5) s := by
  have memory := Memory.mem_eq_iff_read_mem_bytes_eq.mp (clz_start_memory s base)
  have sp : r (.GPR 31#5) (block base clzStartOps s) = r (.GPR 31#5) s - 16#64 := by
    simp [block, clzStartOps, Op.effect, put, next, state_simp_rules]
  dsimp only
  rw [sp, memory, memory]
  simp (disch := delimited_side) [countSlot, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem clz_start_registers (s : ArmState) (base : BitVec 64) (byte : UInt8)
    (nonzero : byte ≠ 0) (input : r (.GPR 8#5) s = BitVec.ofNat 64 byte.toNat) :
    let t := block base clzStartOps s
    read_pc t = base + 104#64 ∧
      (r (.GPR 9#5) t).setWidth 32 = clzInput byte ∧
      (r (.GPR 10#5) t).setWidth 32 = 32#32 ∧
      r (.GPR 23#5) t = r (.GPR 25#5) s >>> 61 ∧
      r (.GPR 25#5) t = r (.GPR 25#5) s ∧
      r (.GPR 3#5) t = r (.GPR 3#5) s ∧
      r (.GPR 31#5) t = r (.GPR 31#5) s - 16#64 := by
  have zero := (clz_byte_facts byte nonzero).2.2 ⟨0, by decide⟩ (by
    change 0 < 25 + Ssz.highestBit byte
    omega)
  simp only [BitVec.ushiftRight_zero, clzInput] at zero
  simp [block, clzStartOps, Op.effect, put, next, state_simp_rules,
    input, clzInput, zero]

private theorem highest_word (byte : UInt8) :
    ((BitVec.ofNat 32 (7 - Ssz.highestBit byte)) ^^^ 7#32).setWidth 64 =
      BitVec.ofNat 64 (Ssz.highestBit byte) := by
  have bit := SszNative.BitView.highestBit_lt byte
  have xor := clz_highest byte
  have count : 32 - (25 + Ssz.highestBit byte) = 7 - Ssz.highestBit byte := by omega
  rw [count] at xor
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, xor, BitVec.toNat_ofNat]

/-- Opaque exit of the real restored-lowering/CMP/EOR/ORR/B.HS count block. The
small/large dispatch is exactly the native from_u128 threshold. -/
theorem count_exit (s : ArmState) (base : BitVec 64) (byte : UInt8) (length : Nat)
    (physical : length < 2^64)
    (inputLength : r (.GPR 3#5) s = BitVec.ofNat 64 length)
    (hprefix : r (.GPR 25#5) s = BitVec.ofNat 64 (length - 1))
    (counter : (r (.GPR 10#5) s).setWidth 32 = BitVec.ofNat 32 (7 - Ssz.highestBit byte))
    (threshold : read_mem_bytes 8 (r (.GPR 31#5) s) s = countThreshold) :
    let t := block base countOps s
    r (.GPR 24#5) t = BitVec.ofNat 64 (8 * (length - 1) + Ssz.highestBit byte) ∧
      r (.GPR 26#5) t = BitVec.ofNat 64 (7 - Ssz.highestBit byte) ∧
      r (.GPR 31#5) t = r (.GPR 31#5) s + 16#64 ∧
      read_pc t = if 2^61 < length then base + 268#64 else base + 148#64 := by
  have bit := SszNative.BitView.highestBit_lt byte
  have highest := highest_word byte
  have join := count_low_word length (Ssz.highestBit byte) physical bit
  have carry : (AddWithCarry (BitVec.ofNat 64 length) (~~~countThreshold) 1#1).2.c = 1#1 ↔
      2^61 < length := by
    rw [Udivti3.cmp_carry]
    simp only [countThreshold, BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical]
    omega
  have widened : (BitVec.ofNat 32 (7 - Ssz.highestBit byte)).setWidth 64 =
      BitVec.ofNat 64 (7 - Ssz.highestBit byte) :=
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)
  have highestWide : BitVec.ofNat 64 (7 - Ssz.highestBit byte) ^^^ 7#64 =
      BitVec.ofNat 64 (Ssz.highestBit byte) := by
    have cast7 : (7#32).setWidth 64 = 7#64 := by decide
    simpa only [BitVec.setWidth_xor, widened, cast7] using highest
  simp [block, countOps, Op.effect, put, next, state_simp_rules,
    counter, threshold, inputLength, hprefix, highestWide, join, carry, BitVec.add_assoc, widened]

end SszArm.Delimited
