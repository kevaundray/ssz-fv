import SszX86.IndicesPrefixEqualSteps
import SszX86.IndicesPrefixEqualOwned
import SszX86.DispatchMemory
import SszX86.BoolReturn

namespace SszX86.IndicesPrefixEqual
open BoolCodec UintCodec

macro "indices_prefix_push " row:num ", " off:num " using " hc:term ", " hm:term : tactic => `(tactic|
  (indices_prefix_step $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · have mapped := $hm
     apply SszX86.Dispatch.push_load (offset := $off)
     · repeat' first | exact mapped | apply Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

/-- The six physical PUSHes start at the original entry and establish the
saved-register image used by the epilogue, with arbitrary prior stack bytes. -/
theorem pushes_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (next : Eventually (step e) P (Dispatch.savedState s, base + 10)) :
    Eventually (step e) P (s, base) := by
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 - 8 = s.regs.rsp - 48 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat, BitVec.sub_sub]
    rfl
  suffices run : Eventually (step e) P (s, base + 0) by
    simpa only [Int64.add_zero] using run
  indices_prefix_push 0, 8 using hc, mapped
  indices_prefix_push 1, 16 using hc, mapped
  indices_prefix_push 2, 24 using hc, mapped
  indices_prefix_push 3, 32 using hc, mapped
  indices_prefix_push 4, 40 using hc, mapped
  indices_prefix_push 5, 48 using hc, mapped
  simpa [Dispatch.savedState, Dispatch.savedMem, Width.bytesv, BitVec.sub_sub, stackReg]
    using next

def allocated (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 24)},
    status := flags}

theorem allocate_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (allocated s flags, base + 14)) :
    Eventually (step e) P (s, base + 10) := by
  indices_prefix_step 6 using hc
  simpa [allocated] using next _

/-- The saved words are at24..64 above the local pointer; RET reads at72. -/
def SavedAt (m : DataMem) (sp : BitVec 64) (saved : Dispatch.Saved) : Prop :=
  Mem.loadInt m (sp + 24#64) 8 = some (Int.ofBytes (wordBytes saved.rbx)) ∧
  Mem.loadInt m (sp + 32#64) 8 = some (Int.ofBytes (wordBytes saved.r12)) ∧
  Mem.loadInt m (sp + 40#64) 8 = some (Int.ofBytes (wordBytes saved.r13)) ∧
  Mem.loadInt m (sp + 48#64) 8 = some (Int.ofBytes (wordBytes saved.r14)) ∧
  Mem.loadInt m (sp + 56#64) 8 = some (Int.ofBytes (wordBytes saved.r15)) ∧
  Mem.loadInt m (sp + 64#64) 8 = some (Int.ofBytes (wordBytes saved.rbp)) ∧
  Mem.loadInt m (sp + 72#64) 8 = some (Int.ofBytes (wordBytes saved.rip))

def returnedState (s : MachineData) (saved : Dispatch.Saved) : MachineData :=
  {s with regs := {s.regs with
    rbx := UInt64.ofBitVec saved.rbx, r12 := UInt64.ofBitVec saved.r12,
    r13 := UInt64.ofBitVec saved.r13, r14 := UInt64.ofBitVec saved.r14,
    r15 := UInt64.ofBitVec saved.r15, rbp := UInt64.ofBitVec saved.rbp,
    rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 80#64)},
    status := Udivti3.addFlags 24#64 s.regs.rsp.toBitVec}

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "indices_prefix_pop " row:num " using " hc:term " word " hw:term : tactic => `(tactic|
  (indices_prefix_step $row using $hc
   simp [MachineData.load, Effects.All, ($hw), SszX86.ofBytes_wordBytes,
     BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

/-- The actual common ADD24/six-POP/RET epilogue, with no model-return step. -/
theorem epilogue (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Dispatch.Saved)
    (stored : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (P : MachineState → Prop)
    (next : P (returnedState s saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 1247) := by
  rcases stored with ⟨rbx, r12, r13, r14, r15, rbp, rip⟩
  indices_prefix_step 365 using hc
  indices_prefix_pop 366 using hc word rbx
  indices_prefix_pop 367 using hc word r12
  indices_prefix_pop 368 using hc word r13
  indices_prefix_pop 369 using hc word r14
  indices_prefix_pop 370 using hc word r15
  indices_prefix_pop 371 using hc word rbp
  indices_prefix_pop 372 using hc word rip
  have carry :
      ((s.regs.rsp.toBitVec + 24#64).unsigned !=
        (24#64).unsigned + s.regs.rsp.toBitVec.unsigned) =
        decide (Udivti3.radix ≤ 24 + s.regs.rsp.toNat) := by
    simpa [Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      Udivti3.addFlags_cf 24#64 s.regs.rsp.toBitVec
  simpa [returnedState, Udivti3.addFlags, BitVec.take, BitVec.signed,
    BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
    show (8 : UInt64) + 72 = 80 by decide] using (Eventually.done _ next)

end SszX86.IndicesPrefixEqual
