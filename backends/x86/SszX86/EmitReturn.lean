import SszX86.EmitCore
import SszX86.BoolReturn

namespace SszX86.Emit
open BoolCodec

/-- The emitter's six saved words and the original caller return slot. -/
def SavedAt (m : DataMem) (sp : BitVec 64) (saved : Saved) : Prop :=
  Mem.loadInt m (sp + 104#64) 8 = some (Int.ofBytes (wordBytes saved.rbx)) ∧
  Mem.loadInt m (sp + 112#64) 8 = some (Int.ofBytes (wordBytes saved.r12)) ∧
  Mem.loadInt m (sp + 120#64) 8 = some (Int.ofBytes (wordBytes saved.r13)) ∧
  Mem.loadInt m (sp + 128#64) 8 = some (Int.ofBytes (wordBytes saved.r14)) ∧
  Mem.loadInt m (sp + 136#64) 8 = some (Int.ofBytes (wordBytes saved.r15)) ∧
  Mem.loadInt m (sp + 144#64) 8 = some (Int.ofBytes (wordBytes saved.rbp)) ∧
  Mem.loadInt m (sp + 152#64) 8 = some (Int.ofBytes (wordBytes saved.rip))

def returned (s : MachineData) (saved : Saved) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := UInt64.ofBitVec saved.rbx
      r12 := UInt64.ofBitVec saved.r12
      r13 := UInt64.ofBitVec saved.r13
      r14 := UInt64.ofBitVec saved.r14
      r15 := UInt64.ofBitVec saved.r15
      rbp := UInt64.ofBitVec saved.rbp
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 160#64)}
    status := Udivti3.addFlags 104#64 s.regs.rsp.toBitVec}

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "emit_pop " row:num " using " hc:term " word " hw:term : tactic => `(tactic|
  (emit_step $row using $hc
   simp [MachineData.load, Effects.All, ($hw), SszX86.ofBytes_wordBytes,
     BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

/-- Actual ADD104/six-POP/RET, consuming the original caller return slot. -/
theorem epilogue (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved)
    (hs : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (P : MachineState → Prop)
    (hp : P (returned s saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 1600) := by
  rcases hs with ⟨hrbx, hr12, hr13, hr14, hr15, hrbp, hrip⟩
  emit_step 268 using hc
  emit_pop 269 using hc word hrbx
  emit_pop 270 using hc word hr12
  emit_pop 271 using hc word hr13
  emit_pop 272 using hc word hr14
  emit_pop 273 using hc word hr15
  emit_pop 274 using hc word hrbp
  emit_pop 275 using hc word hrip
  have carry :
      ((s.regs.rsp.toBitVec + 104#64).unsigned !=
        (104#64).unsigned + s.regs.rsp.toBitVec.unsigned) =
        decide (Udivti3.radix ≤ 104 + s.regs.rsp.toNat) := by
    simpa [Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      Udivti3.addFlags_cf 104#64 s.regs.rsp.toBitVec
  simpa [returned, Udivti3.addFlags, BitVec.take, BitVec.signed,
    BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
    show (8 : UInt64) + 152 = 160 by decide]
    using (Eventually.done _ hp)

def successState (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (s.regs.rbx.toBitVec + 64) 4 0}

theorem status_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hmap : UintCodec.Large.Mapped s.dmem (s.regs.rbx.toBitVec + 64) 4)
    (next : Eventually (step e) P (successState s, base + 1600)) :
    Eventually (step e) P (s, base + 1593) := by
  emit_step 267 using hc
  apply Delimited.store_cps
  · simpa only [BitVec.add_zero, show (64 : BitVec 64) = 64#64 by decide,
      show Width.W32.bytes = 4 by rfl] using
      UintCodec.Large.mapped_load s.dmem (s.regs.rbx.toBitVec + 64) 4 0 4 hmap (by decide)
  simpa only [Effects.All, successState, show (64 : BitVec 64) = 64#64 by decide,
    show Width.W32.bytes = 4 by rfl, show (0#32).toInt = 0 by decide] using next

end SszX86.Emit
