import SszX86.MeasureCore
import SszX86.BoolReturn

namespace SszX86.Measure
open BoolCodec

/-- The measurement activation's six saved words and the original caller return slot. -/
def SavedAt (m : DataMem) (sp : BitVec 64) (saved : Saved) : Prop :=
  Mem.loadInt m (sp + 216#64) 8 = some (Int.ofBytes (wordBytes saved.rbx)) ∧
  Mem.loadInt m (sp + 224#64) 8 = some (Int.ofBytes (wordBytes saved.r12)) ∧
  Mem.loadInt m (sp + 232#64) 8 = some (Int.ofBytes (wordBytes saved.r13)) ∧
  Mem.loadInt m (sp + 240#64) 8 = some (Int.ofBytes (wordBytes saved.r14)) ∧
  Mem.loadInt m (sp + 248#64) 8 = some (Int.ofBytes (wordBytes saved.r15)) ∧
  Mem.loadInt m (sp + 256#64) 8 = some (Int.ofBytes (wordBytes saved.rbp)) ∧
  Mem.loadInt m (sp + 264#64) 8 = some (Int.ofBytes (wordBytes saved.rip))

def returned (s : MachineData) (saved : Saved) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := UInt64.ofBitVec saved.rbx
      r12 := UInt64.ofBitVec saved.r12
      r13 := UInt64.ofBitVec saved.r13
      r14 := UInt64.ofBitVec saved.r14
      r15 := UInt64.ofBitVec saved.r15
      rbp := UInt64.ofBitVec saved.rbp
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 272#64)}
    status := Udivti3.addFlags 216#64 s.regs.rsp.toBitVec}

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "measure_pop " row:num " using " hc:term " word " hw:term : tactic => `(tactic|
  (measure_step $row using $hc
   simp [MachineData.load, Effects.All, ($hw), SszX86.ofBytes_wordBytes,
     BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

/-- Actual ADD216/six-POP/RET, consuming the original caller return slot. -/
theorem epilogue (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved)
    (hs : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (P : MachineState → Prop)
    (hp : P (returned s saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 3335) := by
  rcases hs with ⟨hrbx, hr12, hr13, hr14, hr15, hrbp, hrip⟩
  measure_step 468 using hc
  measure_pop 469 using hc word hrbx
  measure_pop 470 using hc word hr12
  measure_pop 471 using hc word hr13
  measure_pop 472 using hc word hr14
  measure_pop 473 using hc word hr15
  measure_pop 474 using hc word hrbp
  measure_pop 475 using hc word hrip
  have carry :
      ((s.regs.rsp.toBitVec + 216#64).unsigned !=
        (216#64).unsigned + s.regs.rsp.toBitVec.unsigned) =
        decide (Udivti3.radix ≤ 216 + s.regs.rsp.toNat) := by
    simpa [Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      Udivti3.addFlags_cf 216#64 s.regs.rsp.toBitVec
  simpa [returned, Udivti3.addFlags, BitVec.take, BitVec.signed,
    BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
    show (8 : UInt64) + 264 = 272 by decide]
    using (Eventually.done _ hp)

end SszX86.Measure
