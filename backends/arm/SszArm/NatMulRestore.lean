import SszArm.NatMulRestoreRegisters

namespace SszArm.NatMul

open Delimited (Returned)

theorem restore_run (path : RestorePath) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.start) :
    run path.ops.length s = restored path s base := by
  apply block_run base path.ops s code error aligned
  have hpc : r .PC s = base + BitVec.ofNat 64 path.start := pc
  cases path <;> simp [Follows, RestorePath.ops, RestorePath.start, Op.row, Op.effect,
    put, next, state_simp_rules, hpc, BitVec.add_assoc]

@[simp] theorem restore_memory (path : RestorePath) (s : ArmState) (base : BitVec 64) :
    (restored path s base).mem = s.mem := by
  cases path <;> simp [restored, RestorePath.ops, block, Op.effect, put, next, state_simp_rules]

theorem restore_registers (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) (reg : BitVec 5) (low : 19 ≤ reg.toNat) (high : reg.toNat ≤ 30) :
    r (.GPR reg) (restored path s base) = r (.GPR reg) entry := by
  have member : reg = 19#5 ∨ reg = 20#5 ∨ reg = 21#5 ∨ reg = 22#5 ∨
      reg = 23#5 ∨ reg = 24#5 ∨ reg = 25#5 ∨ reg = 26#5 ∨
      reg = 27#5 ∨ reg = 28#5 ∨ reg = 29#5 ∨ reg = 30#5 := by bv_omega
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact restore_register_19 path entry s base saved
  · exact restore_register_20 path entry s base saved
  · exact restore_register_21 path entry s base saved
  · exact restore_register_22 path entry s base saved
  · exact restore_register_23 path entry s base saved
  · exact restore_register_24 path entry s base saved
  · exact restore_register_25 path entry s base saved
  · exact restore_register_26 path entry s base saved
  · exact restore_register_27 path entry s base saved
  · exact restore_register_28 path entry s base saved
  · exact restore_register_29 path entry s base saved
  · exact restore_register_30 path entry s base saved

theorem restore_stack (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) : r (.GPR 31#5) (restored path s base) = r (.GPR 31#5) entry := by
  cases path <;> simp [restored, RestorePath.ops, block, Op.effect, put, next,
    state_simp_rules, saved.sp, BitVec.sub_add_cancel]

theorem return_restored (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) (error : read_err s = .None) :
    Returned entry (restored .return s base) := by
  have h30 := saved.words 30#5 0 (by decide)
  simp only [BitVec.add_zero] at h30
  refine ⟨?_, (block_error _ _ _).trans error, restore_stack .return entry s base saved,
    restore_registers .return entry s base saved, ?_⟩
  · simp [restored, RestorePath.ops, block, Op.effect, put, next, state_simp_rules, h30]
  · intro reg low high
    simpa [restored, RestorePath.ops, block, Op.effect, put, next, state_simp_rules] using
      saved.vectors reg low high

theorem tail_restored (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    read_pc (restored .tail s base) = base + wordOffset ∧
      r (.GPR 0#5) (restored .tail s base) = r (.GPR 0#5) s ∧
      r (.GPR 1#5) (restored .tail s base) = r (.GPR 1#5) s ∧
      r (.GPR 2#5) (restored .tail s base) = r (.GPR 2#5) s ∧
      r (.GPR 3#5) (restored .tail s base) = r (.GPR 3#5) s ∧
      r (.GPR 4#5) (restored .tail s base) = r (.GPR 5#5) s ∧
      r (.GPR 31#5) (restored .tail s base) = r (.GPR 31#5) entry ∧
      (∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 30 →
        r (.GPR reg) (restored .tail s base) = r (.GPR reg) entry) := by
  refine ⟨?_, restore_argument_0 .tail s base, restore_argument_1 .tail s base,
    restore_argument_2 .tail s base, restore_argument_3 .tail s base,
    restore_tail_argument_4 s base, restore_stack .tail entry s base saved,
    restore_registers .tail entry s base saved⟩
  simp [restored, RestorePath.ops, block, Op.effect, put, next,
    state_simp_rules, wordOffset]

end SszArm.NatMul
