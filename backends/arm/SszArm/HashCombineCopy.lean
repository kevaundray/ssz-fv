import SszArm.HashCombineCalls

namespace SszArm.Hash.Combine

open Delimited (MemoryFrame)

def copySetupOps : List Op := [.p364, .p368, .p372]

@[irreducible] def copySetup (s : ArmState) : ArmState := block copySetupOps s

theorem copySetup_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 364#64) : run 3 s = copySetup s := by
  have follows : Follows base copySetupOps s := by
    change r .PC s = _ at pc
    simp [Follows, copySetupOps, Op.row, Op.effect, put, next,
      state_simp_rules, aligned, pc, BitVec.add_assoc]
  rw [copySetup]
  exact runs copySetupOps s base code error follows

@[simp] theorem copySetup_program (s : ArmState) : (copySetup s).program = s.program := by
  simp only [copySetup, block_program]

@[simp] theorem copySetup_error (s : ArmState) : read_err (copySetup s) = read_err s := by
  simp only [copySetup, block_error]

@[simp] theorem copySetup_memory (s : ArmState) : (copySetup s).mem = s.mem := by
  simp [copySetup, copySetupOps, block, Op.effect, put, next, state_simp_rules]

@[simp] theorem copySetup_register (s : ArmState) (reg : BitVec 5)
    (different : reg ∉ [0#5, 1#5, 2#5]) : r (.GPR reg) (copySetup s) = r (.GPR reg) s := by
  have h0 : reg ≠ 0#5 := by simp_all
  have h1 : reg ≠ 1#5 := by simp_all
  have h2 : reg ≠ 2#5 := by simp_all
  simp [copySetup, copySetupOps, block, Op.effect, put, next, state_simp_rules, h0, h1, h2]

@[simp] theorem copySetup_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (copySetup s) = r (.SFP reg) s := by
  simp [copySetup, copySetupOps, block, Op.effect, put, next, state_simp_rules]

theorem copySetup_arguments (s : ArmState) :
    r (.GPR 0#5) (copySetup s) = r (.GPR 31#5) s + 112#64 ∧
    r (.GPR 1#5) (copySetup s) = r (.GPR 31#5) s ∧
    r (.GPR 2#5) (copySetup s) = 112#64 := by
  simp [copySetup, copySetupOps, block, Op.effect, put, next, state_simp_rules]

theorem stateAt_mem_eq {s t : ArmState} {address : BitVec 64} {value : StreamState}
    (memory : t.mem = s.mem) (source : StateAt s address value) : StateAt t address value := by
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp memory
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [BytesAt, memory] using source.buffer
  · simpa only [ChainingAt, reads] using source.chaining
  · exact (reads 8 _).trans source.buffered
  · exact (reads 8 _).trans source.byteLen

structure StateCopyPost (s t : ArmState) (base : BitVec 64) (value : StreamState) : Prop where
  pc : read_pc t = base + 380#64
  error : read_err t = .None
  program : t.program = s.program
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 29 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64
  state : StateAt t (r (.GPR 31#5) s + 112#64) value
  frame : MemoryFrame [((r (.GPR 31#5) s + 112#64).toNat, 112)] s t

/-- The native wrapper copies all112 bytes before calling the finalizer; it does
not finalize the update state in place and does not reconstruct a32-byte state. -/
theorem state_copy_correct (s : ArmState) (base : BitVec 64) (value : StreamState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 364#64)
    (physical : (r (.GPR 31#5) s).toNat + 224 ≤ 2^64)
    (source : StateAt s (r (.GPR 31#5) s) value) :
    StateCopyPost s (run (3 + (Memcpy.fuel 112 + 1)) s) base value := by
  let a := copySetup s
  have arguments : r (.GPR 0#5) a = r (.GPR 31#5) s + 112#64 ∧
      r (.GPR 1#5) a = r (.GPR 31#5) s ∧ r (.GPR 2#5) a = 112#64 :=
    copySetup_arguments s
  have length : (r (.GPR 2#5) a).toNat = 112 := by rw [arguments.2.2]; rfl
  have aPC : read_pc a = base + 376#64 := by
    change r .PC s = _ at pc
    simp [a, copySetup, copySetupOps, block, Op.effect, put, next,
      state_simp_rules, pc, BitVec.add_assoc]
  have aAligned : CheckSPAlignment a := by
    simpa [a, copySetup, copySetupOps, block, Op.effect, put, next,
      state_simp_rules] using aligned
  have aError : read_err a = .None := (copySetup_error s).trans error
  have dstBound : (r (.GPR 0#5) a).toNat + 112 ≤ 2^64 := by
    rw [arguments.1]
    bv_omega
  have srcBound : (r (.GPR 1#5) a).toNat + 112 ≤ 2^64 := by
    rw [arguments.2.1]
    omega
  have separate : Memcpy.Disjoint (r (.GPR 0#5) a) (r (.GPR 1#5) a) 112 := by
    right
    rw [arguments.1, arguments.2.1]
    bv_omega
  have copied := copy_correct .state a base (code.of_program_eq (copySetup_program s))
    aPC aError aAligned (by simpa only [length] using dstBound)
    (by simpa only [length] using srcBound) (by simpa only [length] using separate)
  simp only [length] at copied
  have sourceA : StateAt a (r (.GPR 1#5) a) value := by
    rw [arguments.2.1]
    exact stateAt_mem_eq (copySetup_memory s) source
  have resultState := copied.state length sourceA dstBound srcBound
  rw [run_plus, copySetup_run s base code error aligned pc]
  refine ⟨?_, copied.error, copied.program.trans (copySetup_program s), ?_, ?_, ?_, ?_, ?_⟩
  · rw [copied.pc, aPC]
    simp only [BitVec.add_assoc, show 376#64 + 4#64 = 380#64 by decide]
  · exact (copied.registers 31#5 (by decide)).trans (copySetup_register s 31#5 (by decide))
  · intro reg lo hi
    exact (copied.registers reg (by simp only [List.mem_cons, List.not_mem_nil, or_false]; bv_omega)).trans
      (copySetup_register s reg (by simp only [List.mem_cons, List.not_mem_nil, or_false]; bv_omega))
  · intro reg lo hi
    rw [copied.vectors reg (by bv_omega), copySetup_vector]
  · simpa only [arguments.1] using resultState
  · intro address outside
    have observed := copied.frame address (by simpa only [arguments.1, length] using outside)
    exact observed.trans (congrFun (copySetup_memory s) address)

end SszArm.Hash.Combine
