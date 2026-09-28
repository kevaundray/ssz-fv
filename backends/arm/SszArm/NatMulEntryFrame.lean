import SszArm.NatMulEntrySaved

namespace SszArm.NatMul

open Delimited (MemoryFrame Protected)

def entryWrites (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 31#5) s).toNat - 144, 144)]

theorem entry_local_covered (s : ArmState)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) :
    BitVector.Covers (localWrites s result) (entryWrites s) := by
  intro span member
  simp only [entryWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  subst span
  refine ⟨((r (.GPR 31#5) s).toNat - 144, 144), ?_, le_rfl, le_rfl⟩
  cases value : result.result <;> simp [localWrites, value]

theorem entry_covered (s : ArmState)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) :
    BitVector.Covers (writesFor s result) (entryWrites s) := by
  intro span member
  obtain ⟨outer, outerMember, low, high⟩ := entry_local_covered s result span member
  refine ⟨outer, ?_, low, high⟩
  cases allocation : result.allocation <;> simp [writesFor, allocation, outerMember]

structure EntryFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  output : r (.GPR 0#5) t = r (.GPR 0#5) s
  arena : r (.GPR 5#5) t = r (.GPR 5#5) s
  saved : Saved s t
  memory : MemoryFrame (entryWrites s) s t

theorem EntryFrame.sp {s t : ArmState} (frame : EntryFrame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s - 96#64 := frame.saved.sp

theorem EntryFrame.code {s t : ArmState} (frame : EntryFrame s t) {base : BitVec 64}
    (code : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, frame.program] using code

theorem EntryFrame.jointCode {s t : ArmState} (frame : EntryFrame s t) {base : BitVec 64}
    (code : JointCodeAt s base) : JointCodeAt t base := code.transport frame.program

theorem EntryFrame.aligned {s t : ArmState} (frame : EntryFrame s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  have first : CheckSPAlignment (activated s) := by
    rw [← save_effect s 0#64]
    exact block_aligned _ _ _ aligned
  have equalSP : r (.GPR 31#5) t = r (.GPR 31#5) (activated s) := by
    rw [activated_sp, frame.sp]
  simpa only [CheckSPAlignment, state_simp_rules, equalSP] using first

theorem EntryFrame.memoryFor {s t : ArmState} (frame : EntryFrame s t)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) :
    MemoryFrame (writesFor s result) s t := (entry_covered s result).frame frame.memory

theorem entry_activation (s : ArmState) (stack : 144 ≤ (r (.GPR 31#5) s).toNat) :
    EntryFrame s (activated s) := by
  refine ⟨activated_program s, activated_error s, activated_registers s 0#5 (by decide),
    activated_registers s 5#5 (by decide), activated_saved s (by omega), ?_⟩
  have cover : BitVector.Covers (entryWrites s) (activationWrites s) := by
    intro span member
    simp only [activationWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    subst span
    exact ⟨((r (.GPR 31#5) s).toNat - 144, 144), by simp [entryWrites], by omega, by omega⟩
  exact cover.frame (activation_frame s (by omega))

theorem EntryFrame.dispatch {s u t : ArmState} (first : EntryFrame s u)
    (stack : 144 ≤ (r (.GPR 31#5) s).toNat) (last : DispatchFrame u t) : EntryFrame s t := by
  refine ⟨last.program.trans first.program, last.error.trans first.error,
    (last.registers 0#5 (by decide)).trans first.output,
    (last.registers 5#5 (by decide)).trans first.arena, first.saved.dispatch stack last, ?_⟩
  have cover : BitVector.Covers (entryWrites s) [((r (.GPR 31#5) u).toNat - 16, 16)] := by
    intro span member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst span
    refine ⟨((r (.GPR 31#5) s).toNat - 144, 144), by simp [entryWrites], ?_, ?_⟩
    · rw [first.sp]; bv_omega
    · rw [first.sp]; bv_omega
  exact first.memory.trans (cover.frame last.memoryFrame)

end SszArm.NatMul
