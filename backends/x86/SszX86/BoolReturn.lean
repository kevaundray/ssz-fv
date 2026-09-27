import SszX86.BoolExec
import SszX86.Udivti3Math

namespace SszX86.BoolCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Saved callee state plus the return address slot consumed by the epilogue. -/
structure Saved where
  rbx : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64
  rbp : BitVec 64
  rip : BitVec 64

/-- Actual epilogue stack image at the prepared body's stack pointer. -/
def SavedAt (m : DataMem) (sp : BitVec 64) (saved : Saved) : Prop :=
  Mem.loadInt m (sp + 312#64) 8 = some (Int.ofBytes (SszX86.wordBytes saved.rbx)) ∧
  Mem.loadInt m (sp + 320#64) 8 = some (Int.ofBytes (SszX86.wordBytes saved.r12)) ∧
  Mem.loadInt m (sp + 328#64) 8 = some (Int.ofBytes (SszX86.wordBytes saved.r13)) ∧
  Mem.loadInt m (sp + 336#64) 8 = some (Int.ofBytes (SszX86.wordBytes saved.r14)) ∧
  Mem.loadInt m (sp + 344#64) 8 = some (Int.ofBytes (SszX86.wordBytes saved.r15)) ∧
  Mem.loadInt m (sp + 352#64) 8 = some (Int.ofBytes (SszX86.wordBytes saved.rbp)) ∧
  Mem.loadInt m (sp + 360#64) 8 = some (Int.ofBytes (SszX86.wordBytes saved.rip))

/-- Post-epilogue machine state: memory and vectors preserved; callee-saved
registers restored from the actual saved frame; `rsp` advanced by 368; status is
exactly the `addq $0x138,%rsp` flags. -/
def returned (s : MachineData) (saved : Saved) : MachineData :=
  { s with
    regs := { s.regs with
      rbx := UInt64.ofBitVec saved.rbx
      r12 := UInt64.ofBitVec saved.r12
      r13 := UInt64.ofBitVec saved.r13
      r14 := UInt64.ofBitVec saved.r14
      r15 := UInt64.ofBitVec saved.r15
      rbp := UInt64.ofBitVec saved.rbp
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 368#64) }
    status := SszX86.Udivti3.addFlags 312#64 s.regs.rsp.toBitVec }

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "bool_pop " row:num " using " hc:term " word " hw:term : tactic => `(tactic|
  (bool_step $row using $hc
   simp [MachineData.load, Effects.All, ($hw), SszX86.ofBytes_wordBytes,
     BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

/-- Actual Boolean epilogue: `add rsp, 312; pop rbx; pop r12; pop r13; pop r14;
pop r15; pop rbp; ret`. The proof uses the pinned instruction bytes, the real
`popq`/`retq` semantics, and the saved activation frame at the original stack
pointer. -/
theorem epilogue (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved)
    (hs : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (P : MachineState → Prop)
    (hp : P (returned s saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 7720) := by
  rcases hs with ⟨hrbx, hr12, hr13, hr14, hr15, hrbp, hrip⟩
  bool_step 35 using hc
  bool_pop 36 using hc word hrbx
  bool_pop 37 using hc word hr12
  bool_pop 38 using hc word hr13
  bool_pop 39 using hc word hr14
  bool_pop 40 using hc word hr15
  bool_pop 41 using hc word hrbp
  bool_pop 42 using hc word hrip
  have carry :
      ((s.regs.rsp.toBitVec + 312#64).unsigned !=
        (312#64).unsigned + s.regs.rsp.toBitVec.unsigned) =
        decide (SszX86.Udivti3.radix ≤ 312 + s.regs.rsp.toNat) := by
    simpa [SszX86.Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      SszX86.Udivti3.addFlags_cf 312#64 s.regs.rsp.toBitVec
  simpa [returned, SszX86.Udivti3.addFlags, BitVec.take, BitVec.signed,
    BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
    show (8 : UInt64) + 360 = 368 by decide]
    using (Eventually.done _ hp)

end SszX86.BoolCodec
