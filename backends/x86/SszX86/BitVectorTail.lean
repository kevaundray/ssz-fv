import SszX86.BitVectorChecks

namespace SszX86.BitVector

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def tailLoadState (s : MachineData) (byte : BitVec 8) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec (byte.setWidth 64)}}

/-- The only input access in the body loads source[len-1], after exact and the
nonzero-remainder/nonempty gate. The caller supplies that physical byte read. -/
theorem tail_load_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer : BitVec 64) (byte : BitVec 8)
    (hsource : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 104#64) 8 = some (pointer.toNat : Int))
    (hbyte : Mem.loadInt s.dmem (pointer + s.regs.r14.toBitVec - 1#64) 1 = some (byte.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (tailLoadState s byte, base + 4863)) :
    Eventually (step e) P (s, base + 4852) := by
  have byteRead : Mem.loadInt s.dmem
      (pointer + s.regs.r14.toBitVec + 18446744073709551615#64) 1 = some (byte.toNat : Int) := by
    simpa only [BitVec.sub_eq_add_neg, show -(1#64) = 18446744073709551615#64 by decide] using hbyte
  bitvector_step 149 using hc
  bitvector_load hsource
  bitvector_step 150 using hc
  simpa [MachineData.load, Effects.All, Width.bytes, Width.bits,
    BitVec.ofInt_add, BitVec.ofInt_toInt, byteRead, Delimited.byte_cast,
    tailLoadState] using next

theorem remainder_byte_mask (remainder : BitVec 64) (bound : remainder.toNat < 8) :
    (remainder.extractLsb' 8 56 ++ (remainder.setWidth 8 &&& 7#8)) = remainder := by
  have alternatives : remainder = 0#64 ∨ remainder = 1#64 ∨
      remainder = 2#64 ∨ remainder = 3#64 ∨ remainder = 4#64 ∨
      remainder = 5#64 ∨ remainder = 6#64 ∨ remainder = 7#64 := by
    bv_omega
  rcases alternatives with h | h | h | h | h | h | h | h <;> subst remainder <;> decide

theorem remainder_word_cast (remainder : BitVec 64) (bound : remainder.toNat < 8) :
    (remainder.setWidth 32).setWidth 64 = remainder := by
  bv_omega

def tailMaskState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rcx := s.regs.r13}, status := flags}

/-- The native low-byte mask is harmless because the real divider returns r<8. -/
theorem tail_mask_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (bound : s.regs.r13.toBitVec.toNat < 8)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (tailMaskState s flags, base + 4870)) :
    Eventually (step e) P (s, base + 4863) := by
  have mask := remainder_byte_mask s.regs.r13.toBitVec bound
  have wordCast := remainder_word_cast s.regs.r13.toBitVec bound
  bitvector_step 151 using hc
  constructor <;> bitvector_step 152 using hc
  all_goals simpa [tailMaskState, BitVec.replaceLow, BitVec.drop, BitVec.take,
    mask, wordCast] using next _

end SszX86.BitVector
