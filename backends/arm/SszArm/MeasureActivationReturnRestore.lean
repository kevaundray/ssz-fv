import SszArm.MeasureActivationReturnOps

namespace SszArm.Measure

open ReturnBlock
open Activation (next put)

def restoreOps : List ReturnBlock.Op := [.p4116, .p4120, .p4124, .p4128, .p4132, .p4136, .p4140]

@[irreducible] def restored (s : ArmState) : ArmState := ReturnBlock.block restoreOps s

@[simp] theorem restored_program (s : ArmState) : (restored s).program = s.program := by
  simp [restored, restoreOps, ReturnBlock.block]

@[simp] theorem restored_error (s : ArmState) : read_err (restored s) = read_err s := by
  simp [restored, restoreOps, ReturnBlock.block]

@[simp] theorem restored_memory (s : ArmState) : (restored s).mem = s.mem := by
  simp [restored, restoreOps, ReturnBlock.block, ReturnBlock.Op.effect, restore, put, next, state_simp_rules]

@[simp] theorem restored_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (restored s) = r (.SFP reg) s := by
  simp [restored, restoreOps, ReturnBlock.block, ReturnBlock.Op.effect, restore, put, next, state_simp_rules]

theorem restored_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 4116#64) : run 7 s = restored s := by
  have upper : Aligned (r (.GPR 31#5) s + 272#64) 4 := by
    simp (config := {decide := true}) [CheckSPAlignment, read_gpr,
      Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
    bv_omega
  rw [restored]
  apply ReturnBlock.runs restoreOps s base code error
  change r .PC s = base + 4116#64 at pc
  simp (config := {decide := true}) [Follows, restoreOps, ReturnBlock.Op.row,
    ReturnBlock.Op.effect, restore, put, next, state_simp_rules, CheckSPAlignment, read_gpr,
    BitVec.setWidth_eq, pc, BitVec.add_assoc] at aligned upper ⊢
  exact ⟨aligned, upper⟩

/-- Internal only: the saved observations are derived from the entry stores and
body frame, never supplied as a private-entry premise. -/
structure RestoreReady (entry current : ArmState) : Prop where
  stack : r (.GPR 31#5) current = (Args.ofEntry entry).bodySP
  saved : ∀ reg offset, (reg, offset) ∈ savedRegisters →
    read_mem_bytes 8 ((Args.ofEntry entry).bodySP + BitVec.ofNat 64 offset) current = r (.GPR reg) entry
  untouched : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5] → r (.GPR reg) current = r (.GPR reg) entry
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) current).setWidth 64 = (r (.SFP reg) entry).setWidth 64

theorem restored_returns (entry s : ArmState) (ready : RestoreReady entry s)
    (error : read_err s = .None) (program : s.program = entry.program) : Returned entry (restored s) := by
  have h29 := ready.saved 29#5 192 (by decide)
  have h30 := ready.saved 30#5 200 (by decide)
  have h26 := ready.saved 26#5 208 (by decide)
  have h25 := ready.saved 25#5 216 (by decide)
  have h24 := ready.saved 24#5 224 (by decide)
  have h23 := ready.saved 23#5 232 (by decide)
  have h22 := ready.saved 22#5 240 (by decide)
  have h21 := ready.saved 21#5 248 (by decide)
  have h20 := ready.saved 20#5 256 (by decide)
  have h19 := ready.saved 19#5 264 (by decide)
  constructor
  · simp [restored, restoreOps, ReturnBlock.block, ReturnBlock.Op.effect, restore, put, next,
      state_simp_rules, BitVec.add_assoc, ready.stack, h30]
  · exact (restored_error s).trans error
  · exact (restored_program s).trans program
  · simp [restored, restoreOps, ReturnBlock.block, ReturnBlock.Op.effect, restore, put, next,
      state_simp_rules, ready.stack, Args.bodySP, Args.ofEntry, BitVec.sub_add_cancel]
  · intro reg low high
    have members : reg = 18#5 ∨ reg = 19#5 ∨ reg = 20#5 ∨ reg = 21#5 ∨ reg = 22#5 ∨
        reg = 23#5 ∨ reg = 24#5 ∨ reg = 25#5 ∨ reg = 26#5 ∨ reg = 27#5 ∨
        reg = 28#5 ∨ reg = 29#5 ∨ reg = 30#5 := by bv_omega
    rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [restored, restoreOps, ReturnBlock.block, ReturnBlock.Op.effect, restore, put, next,
        state_simp_rules, BitVec.add_assoc, ready.stack, h30, h29, h26, h25, h24, h23, h22, h21, h20, h19,
        ready.untouched 18#5 (by decide), ready.untouched 27#5 (by decide), ready.untouched 28#5 (by decide)]
  · intro reg low high
    rw [restored_vector]
    exact ready.vectors reg low high

end SszArm.Measure
