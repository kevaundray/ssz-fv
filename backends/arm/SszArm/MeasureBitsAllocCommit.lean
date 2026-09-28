import SszArm.MeasureBitsAllocReserve
import SszArm.NatExactState

namespace SszArm.Measure.Bits.Alloc

open Delimited (MemoryFrame)

def commitOps : List Op := [.addPointer, .finish0, .finish1, .finish2]

def allocatedPointer (site : Site) (s : ArmState) : BitVec 64 :=
  r (.GPR site.baseReg) s + r (.GPR site.usedReg) s

def committedMemory (site : Site) (s : ArmState) : ArmState :=
  write_mem_bytes 16 (allocatedPointer site s)
    (r (.GPR site.highReg) s ++ r (.GPR site.lowReg) s)
    (write_mem_bytes 8 (r (.GPR 20#5) s + 16#64) (r (.GPR site.workReg) s) s)

def commitResult (site : Site) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (site.entry + 84))
    (w (.GPR site.countReg) 2#64
      (w (.GPR site.pointerReg) (allocatedPointer site s) (committedMemory site s)))

theorem commit_run (site : Site) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (site.entry + 68)) :
    run 4 s = commitResult site s base := by
  have pc' : r .PC s = base + BitVec.ofNat 64 (site.entry + 68) := pc
  have follows : Follows site base commitOps s := by
    cases site <;>
      simp [commitOps, Follows, row, Op.index, effect, put, next, commit,
        storeWords, Site.entry, state_simp_rules, pc', BitVec.add_assoc]
  rw [show 4 = commitOps.length by rfl, block_run site base commitOps s code error aligned follows]
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases site <;> cases field <;>
      simp [commitOps, block, effect, put, next, commit, storeWords,
        commitResult, committedMemory, allocatedPointer, Site.entry, Site.baseReg,
        Site.usedReg, Site.workReg, Site.pointerReg, Site.countReg, Site.lowReg,
        Site.highReg, state_simp_rules, NatExact.r_gpr_w, NatExact.gpr_w_pc,
        pc', BitVec.add_assoc]
  · cases site <;>
      simp [commitOps, block, effect, put, next, commit, storeWords,
        commitResult, committedMemory, state_simp_rules]
  · intro bytes address
    cases site <;>
      simp [commitOps, block, effect, put, next, commit, storeWords,
        commitResult, committedMemory, allocatedPointer, Site.baseReg, Site.usedReg,
        Site.workReg, Site.pointerReg, Site.countReg, Site.lowReg, Site.highReg,
        state_simp_rules, NatCompare.read_spill_w] <;>
      simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes,
        Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

@[simp] theorem commit_program (site : Site) (s : ArmState) (base : BitVec 64) :
    (commitResult site s base).program = s.program := by
  simp [commitResult, committedMemory, state_simp_rules]

@[simp] theorem commit_error (site : Site) (s : ArmState) (base : BitVec 64) :
    read_err (commitResult site s base) = read_err s := by
  simp [commitResult, committedMemory, state_simp_rules]

@[simp] theorem commit_pc (site : Site) (s : ArmState) (base : BitVec 64) :
    read_pc (commitResult site s base) = base + BitVec.ofNat 64 (site.entry + 84) := by
  simp [commitResult, state_simp_rules]

theorem commit_register (site : Site) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (notPointer : reg ≠ site.pointerReg) (notCount : reg ≠ site.countReg) :
    r (.GPR reg) (commitResult site s base) = r (.GPR reg) s := by
  simp [commitResult, committedMemory, state_simp_rules, notPointer, notCount]

@[simp] theorem commit_vector (site : Site) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (commitResult site s base) = r (.SFP reg) s := by
  simp [commitResult, committedMemory, state_simp_rules]

theorem commit_frame (site : Site) (s : ArmState) (base : BitVec 64)
    (header : (r (.GPR 20#5) s).toNat + 24 ≤ 2^64)
    (payload : (allocatedPointer site s).toNat + 16 ≤ 2^64) :
    MemoryFrame [((r (.GPR 20#5) s).toNat + 16, 8),
      ((allocatedPointer site s).toNat, 16)] s (commitResult site s base) := by
  intro address outside
  have cursorOutside := outside ((r (.GPR 20#5) s).toNat + 16, 8) (by simp)
  have payloadOutside := outside ((allocatedPointer site s).toNat, 16) (by simp)
  have cursorNat : (r (.GPR 20#5) s + 16#64).toNat = (r (.GPR 20#5) s).toNat + 16 := by
    bv_omega
  simp only [commitResult, committedMemory, ArmState.mem_w_eq_mem]
  rw [BoolCodec.write_mem_bytes_frame _ _ 16 _ address payload payloadOutside]
  exact BoolCodec.write_mem_bytes_frame s _ 8 _ address
    (by rw [cursorNat]; omega) (by simpa only [cursorNat] using cursorOutside)

end SszArm.Measure.Bits.Alloc
