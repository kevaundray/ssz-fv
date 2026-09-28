import SszX86.BitVectorCore

namespace SszX86.BitVector
open BoolCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "bitvector_pop " row:num " using " hc:term " word " hw:term : tactic => `(tactic|
  (bitvector_step $row using $hc
   simp [MachineData.load, Effects.All, ($hw), SszX86.ofBytes_wordBytes,
     BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

/-- The common native RET is proved against the actual BitVector image. It
restores all six saved registers and consumes the original incoming return slot. -/
theorem epilogue_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved) (hs : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (P : MachineState → Prop)
    (next : P (returned s saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 7720) := by
  rcases hs with ⟨hrbx, hr12, hr13, hr14, hr15, hrbp, hrip⟩
  bitvector_step 220 using hc
  bitvector_pop 221 using hc word hrbx
  bitvector_pop 222 using hc word hr12
  bitvector_pop 223 using hc word hr13
  bitvector_pop 224 using hc word hr14
  bitvector_pop 225 using hc word hr15
  bitvector_pop 226 using hc word hrbp
  bitvector_pop 227 using hc word hrip
  have carry :
      ((s.regs.rsp.toBitVec + 312#64).unsigned !=
        (312#64).unsigned + s.regs.rsp.toBitVec.unsigned) =
        decide (SszX86.Udivti3.radix ≤ 312 + s.regs.rsp.toNat) := by
    simpa [SszX86.Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      SszX86.Udivti3.addFlags_cf 312#64 s.regs.rsp.toBitVec
  simpa [returned, SszX86.Udivti3.addFlags, BitVec.take, BitVec.signed,
    BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
    show (8 : UInt64) + 360 = 368 by decide]
    using (Eventually.done _ next)

end SszX86.BitVector
