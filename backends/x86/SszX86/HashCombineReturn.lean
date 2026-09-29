import SszX86.HashCombineExec
import SszX86.BoolReturn

namespace SszX86.Hash.Combine
open SszX86.WordNormalize

/-- Saved words are outside the in-place 112-byte state and all callee stacks. -/
structure SavedAt (m : DataMem) (sp : BitVec 64) (original : MachineData) : Prop where
  rbx : Mem.loadInt m (sp + 120) 8 =
    some (Int.ofBytes (wordBytes original.regs.rbx.toBitVec))
  r12 : Mem.loadInt m (sp + 128) 8 =
    some (Int.ofBytes (wordBytes original.regs.r12.toBitVec))
  r13 : Mem.loadInt m (sp + 136) 8 =
    some (Int.ofBytes (wordBytes original.regs.r13.toBitVec))
  r14 : Mem.loadInt m (sp + 144) 8 =
    some (Int.ofBytes (wordBytes original.regs.r14.toBitVec))
  r15 : Mem.loadInt m (sp + 152) 8 =
    some (Int.ofBytes (wordBytes original.regs.r15.toBitVec))
  rbp : Mem.loadInt m (sp + 160) 8 =
    some (Int.ofBytes (wordBytes original.regs.rbp.toBitVec))

/-- Only the six actual saved registers are restored; the digest memory and
caller-saved result of finalization remain unchanged. -/
def returnedState (s original : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 176),
    rbx := original.regs.rbx, r12 := original.regs.r12,
    r13 := original.regs.r13, r14 := original.regs.r14,
    r15 := original.regs.r15, rbp := original.regs.rbp}, status := flags}

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "hash_combine_pop " row:num " using " hc:term " savedWord " hw:term : tactic => `(tactic|
  (hash_combine_step $row using $hc
   simp [MachineData.load, Effects.All, ($hw), Delimited.take_cast,
     SszX86.ofBytes_wordBytes, BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

/-- ADD120, six POPs, and the original RET426. This is a return theorem, not
an exit-frontier assertion. -/
theorem epilogue_runs (e : Executable) (root : Int64) (hc : CodeAt e root)
    (s original : MachineData) (ra : BitVec 64)
    (saved : SavedAt s.dmem s.regs.rsp.toBitVec original)
    (slot : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 168) 8 =
      some (Int.ofBytes (wordBytes ra)))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (returnedState s original flags, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, root + 412) := by
  hash_combine_step 88 using hc
  hash_combine_pop 89 using hc savedWord saved.rbx
  hash_combine_pop 90 using hc savedWord saved.r12
  hash_combine_pop 91 using hc savedWord saved.r13
  hash_combine_pop 92 using hc savedWord saved.r14
  hash_combine_pop 93 using hc savedWord saved.r15
  hash_combine_pop 94 using hc savedWord saved.rbp
  hash_combine_pop 95 using hc savedWord slot
  word_simpa [returnedState, BitVec.add_assoc, UInt64.add_assoc,
    show (8 : UInt64) + 168 = 176 by decide,
    show (8 : BitVec 64) + 168 = 176 by decide] using next _

theorem returnedState_abi (s original : MachineData) (flags : StatusFlags)
    (ra : BitVec 64) (sp : s.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 168) :
    Returned original ra (returnedState s original flags, Int64.ofBitVec ra) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [returnedState, UInt64.toBitVec_ofBitVec, sp]
  bv_omega

end SszX86.Hash.Combine
