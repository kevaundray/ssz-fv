import SszX86.BitVectorTail
import SszX86.BitVectorDecode

namespace SszX86.BitVector
open UintCodec BoolCodec
open Kraken.X64.Parser

def tailShiftState (s : MachineData) (byte : BitVec 8) (remainder : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (s.regs.rax.toBitVec.replaceLow (byte >>> remainder.toNat))}
    status := flags}

/-- Actual SHR/TEST/JE, universally quantified over the undefined x86 flags. -/
theorem tail_shift_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (byte : BitVec 8) (remainder : BitVec 64)
    (hcount : s.regs.rcx.toBitVec = remainder)
    (hbyte : s.regs.rax.toBitVec.setWidth 8 = byte)
    (positive : remainder ≠ 0#64) (bound : remainder.toNat < 8)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (tailShiftState s byte remainder flags,
        if byte >>> remainder.toNat = 0#8 then base + 5233 else base + 4880)) :
    Eventually (step e) P (s, base + 4870) := by
  have target := hc.targets ("bitVector_u5233", 5233) (by decide)
  have projection (b : BitVec 8) :
      (s.regs.rax.toBitVec.extractLsb' 8 56 ++ b).setWidth 8 = b :=
    @BitVec.setWidth_append_eq_right 56 8 (s.regs.rax.toBitVec.extractLsb' 8 56) b
  have alternatives : remainder = 1#64 ∨ remainder = 2#64 ∨ remainder = 3#64 ∨
      remainder = 4#64 ∨ remainder = 5#64 ∨ remainder = 6#64 ∨ remainder = 7#64 := by
    bv_omega
  rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals bitvector_decoded_step 153 at 4870 size 2 code parse("shrb %cl,%al") using hc
  all_goals simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take,
    hcount, hbyte, StatusFlags.from_result, Effects.All]
  all_goals repeat' apply And.intro
  all_goals bitvector_decoded_step 154 at 4872 size 2 code parse("testb %al,%al") using hc
  all_goals constructor <;>
    bitvector_decoded_step 155 at 4874 size 6 code parse("je bitVector_u5233") using hc
  all_goals
    split <;> rename_i branch
    all_goals simp [projection, BitVec.take, StatusFlags.from_result] at branch
    all_goals with_reducible
      simpa [tailShiftState, BitVec.replaceLow, BitVec.drop,
        StatusFlags.from_result, Effects.All, *] using next _

/-- The padding failure path recovers the original result pointer from its cache. -/
theorem padding_pointer_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (out : BitVec 64)
    (cached : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (out.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rax := UInt64.ofBitVec out}}, base + 4885)) :
    Eventually (step e) P (s, base + 4880) := by
  bitvector_decoded_step 156 at 4880 size 5 code parse("movq 0x8(%rsp),%rax") using hc
  bitvector_load cached
  exact next

end SszX86.BitVector
