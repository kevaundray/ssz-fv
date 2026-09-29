import SszX86.CodecMeasureFixedCore
import SszX86.BoolReturn

namespace SszX86.CodecMeasureFixed.Output
open BoolCodec UintCodec

structure Saved where
  rbx : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64
  rbp : BitVec 64
  rip : BitVec 64

/-- Only the six saved registers and original return slot are read. -/
def SavedAt (m : DataMem) (sp : BitVec 64) (saved : Saved) : Prop :=
  Mem.loadInt m (sp + 88#64) 8 = some (Int.ofBytes (wordBytes saved.rbx)) ∧
  Mem.loadInt m (sp + 96#64) 8 = some (Int.ofBytes (wordBytes saved.r12)) ∧
  Mem.loadInt m (sp + 104#64) 8 = some (Int.ofBytes (wordBytes saved.r13)) ∧
  Mem.loadInt m (sp + 112#64) 8 = some (Int.ofBytes (wordBytes saved.r14)) ∧
  Mem.loadInt m (sp + 120#64) 8 = some (Int.ofBytes (wordBytes saved.r15)) ∧
  Mem.loadInt m (sp + 128#64) 8 = some (Int.ofBytes (wordBytes saved.rbp)) ∧
  Mem.loadInt m (sp + 136#64) 8 = some (Int.ofBytes (wordBytes saved.rip))

def returned (s : MachineData) (saved : Saved) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := UInt64.ofBitVec saved.rbx
      r12 := UInt64.ofBitVec saved.r12
      r13 := UInt64.ofBitVec saved.r13
      r14 := UInt64.ofBitVec saved.r14
      r15 := UInt64.ofBitVec saved.r15
      rbp := UInt64.ofBitVec saved.rbp
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 144#64)}
    status := Udivti3.addFlags 88#64 s.regs.rsp.toBitVec}

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "codec_fixed_output_pop " row:num " using " code:term " word " word:term : tactic => `(tactic|
  (codec_measure_fixed_step $row using $code
   simp [MachineData.load, Effects.All, ($word), SszX86.ofBytes_wordBytes,
     BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

/-- Actual ADD88, six POPs and RET; memory and SIMD registers are unchanged. -/
theorem epilogue (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (saved : Saved) (stored : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (P : MachineState → Prop)
    (next : P (returned s saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 694) := by
  rcases stored with ⟨rbx, r12, r13, r14, r15, rbp, rip⟩
  codec_measure_fixed_step 174 using code
  codec_fixed_output_pop 175 using code word rbx
  codec_fixed_output_pop 176 using code word r12
  codec_fixed_output_pop 177 using code word r13
  codec_fixed_output_pop 178 using code word r14
  codec_fixed_output_pop 179 using code word r15
  codec_fixed_output_pop 180 using code word rbp
  codec_fixed_output_pop 181 using code word rip
  have carry :
      ((s.regs.rsp.toBitVec + 88#64).unsigned !=
        (88#64).unsigned + s.regs.rsp.toBitVec.unsigned) =
        decide (Udivti3.radix ≤ 88 + s.regs.rsp.toNat) := by
    simpa [Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      Udivti3.addFlags_cf 88#64 s.regs.rsp.toBitVec
  simpa [returned, Udivti3.addFlags, BitVec.take, BitVec.signed,
    BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
    show (8 : UInt64) + 136 = 144 by decide]
    using (Eventually.done _ next)

end SszX86.CodecMeasureFixed.Output
