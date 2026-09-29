import SszX86.HashFinalizeExec

namespace SszX86.Hash.Finalize
open WordNormalize

/-- The finalizer keeps two saved registers and its original caller's slot. -/
def SavedAt (m : DataMem) (localSP rbx r14 ra : BitVec 64) : Prop :=
  Mem.loadInt m (localSP + 8) 8 = some (Int.ofBytes (wordBytes rbx)) ∧
  Mem.loadInt m (localSP + 16) 8 = some (Int.ofBytes (wordBytes r14)) ∧
  Mem.loadInt m (localSP + 24) 8 = some (Int.ofBytes (wordBytes ra))

def returnState (s : MachineData) (rbx r14 : BitVec 64) (flags : StatusFlags) : MachineData :=
  { s with
    regs := { s.regs with
      rbx := UInt64.ofBitVec rbx
      r14 := UInt64.ofBitVec r14
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 32) }
    status := flags }

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "finalize_pop " row:num " using " hc:term " savedWord " hw:term : tactic => `(tactic|
  (hash_finalize_step $row using $hc
   simp [MachineData.load, Width.bytes, Effects.All, ($hw), SszX86.ofBytes_wordBytes,
     WordNormalize.bitvecNumeral, BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

/-- ADD8, POP RBX, POP R14, and the original RET. No success-frontier shortcut. -/
theorem return_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (rbx r14 ra : BitVec 64)
    (saved : SavedAt s.dmem s.regs.rsp.toBitVec rbx r14 ra)
    (P : MachineState → Prop)
    (next : ∀ flags, P (returnState s rbx r14 flags, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 220) := by
  obtain ⟨savedRbx, savedR14, savedRa⟩ := saved
  simp only [WordNormalize.bitvecNumeral] at savedRbx savedR14 savedRa
  hash_finalize_step 62 using hc
  finalize_pop 63 using hc savedWord savedRbx
  finalize_pop 64 using hc savedWord savedR14
  finalize_pop 65 using hc savedWord savedRa
  word_simpa [returnState, BitVec.add_assoc, bv_add_left_comm, BitVec.reduceAdd,
    UInt64.add_assoc, u64_add_left_comm, Effects.All]
    using Eventually.done _ (next _)

/-- Register and memory observations after RET are independent of arithmetic flags. -/
theorem returnState_returned (entry current : MachineData) (ra : BitVec 64)
    (flags : StatusFlags)
    (sp : current.regs.rsp.toBitVec = entry.regs.rsp.toBitVec - 24)
    (rbp : current.regs.rbp = entry.regs.rbp)
    (r12 : current.regs.r12 = entry.regs.r12)
    (r13 : current.regs.r13 = entry.regs.r13)
    (r15 : current.regs.r15 = entry.regs.r15) :
    Returned entry ra (returnState current entry.regs.rbx.toBitVec
      entry.regs.r14.toBitVec flags, Int64.ofBitVec ra) := by
  refine ⟨rfl, ?_, ?_⟩
  · change current.regs.rsp.toBitVec + 32 = entry.regs.rsp.toBitVec + 8
    rw [sp]
    bv_omega
  · exact ⟨rfl, rbp, r12, r13, rfl, r15⟩

end SszX86.Hash.Finalize
