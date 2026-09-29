import SszArm.HashCombineControl
import SszArm.HashCombineMemory

namespace SszArm.Hash.Combine

def fillSetupOps : List Op := [.p196, .p200, .p204, .p208, .p212, .p216, .p220]
def fillResultOps : List Op := [.p228, .p232, .p236, .p240, .p244]
def bufferedSetupOps : List Op := [.p248, .p252, .p256, .p260]

@[irreducible] def fillSetup (s : ArmState) : ArmState := block fillSetupOps s
@[irreducible] def fillResult (s : ArmState) : ArmState := block fillResultOps s
@[irreducible] def bufferedSetup (s : ArmState) : ArmState := block bufferedSetupOps s

theorem fillSetup_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 196#64) : run 7 s = fillSetup s := by
  have follows : Follows base fillSetupOps s := by
    change r .PC s = _ at pc
    simp [Follows, fillSetupOps, Op.row, Op.effect, put, next, compare,
      state_simp_rules, aligned, pc, BitVec.add_assoc]
  rw [fillSetup]
  exact runs fillSetupOps s base code error follows

theorem fillSetup_count (s : ArmState) (buffered : (r (.GPR 22#5) s).toNat < 64) :
    (r (.GPR 23#5) (fillSetup s)).toNat =
      min (64 - (r (.GPR 22#5) s).toNat) (r (.GPR 20#5) s).toNat := by
  have room : (64#64 - r (.GPR 22#5) s).toNat = 64 - (r (.GPR 22#5) s).toNat := by
    bv_omega
  have lower : (AddWithCarry (r (.GPR 20#5) s)
      (~~~(64#64 - r (.GPR 22#5) s)) 1#1).2.c = 1#1 ↔
      64 - (r (.GPR 22#5) s).toNat ≤ (r (.GPR 20#5) s).toNat := by
    simpa only [room] using Udivti3.cmp_carry (r (.GPR 20#5) s) (64#64 - r (.GPR 22#5) s)
  by_cases enough : 64 - (r (.GPR 22#5) s).toNat ≤ (r (.GPR 20#5) s).toNat
  · have carry := lower.mpr enough
    simp (config := {decide := true, instances := true})
      [fillSetup, fillSetupOps, block, Op.effect, put, next, compare,
        state_simp_rules, carry, room, Nat.min_eq_left enough]
  · have carry : (AddWithCarry (r (.GPR 20#5) s)
        (~~~(64#64 - r (.GPR 22#5) s)) 1#1).2.c ≠ 1#1 := by
      intro h
      exact enough (lower.mp h)
    simp (config := {decide := true, instances := true})
      [fillSetup, fillSetupOps, block, Op.effect, put, next, compare,
        state_simp_rules, carry, Nat.min_eq_right (by omega :
          (r (.GPR 20#5) s).toNat ≤ 64 - (r (.GPR 22#5) s).toNat)]

theorem fillSetup_arguments (s : ArmState) :
    r (.GPR 0#5) (fillSetup s) = r (.GPR 25#5) s + r (.GPR 22#5) s ∧
    r (.GPR 1#5) (fillSetup s) = r (.GPR 21#5) s ∧
    r (.GPR 2#5) (fillSetup s) = r (.GPR 23#5) (fillSetup s) := by
  simp [fillSetup, fillSetupOps, block, Op.effect, put, next, compare, state_simp_rules]

@[simp] theorem fillSetup_memory (s : ArmState) : (fillSetup s).mem = s.mem := by
  simp [fillSetup, fillSetupOps, block, Op.effect, put, next, compare, state_simp_rules]

@[simp] theorem fillSetup_program (s : ArmState) : (fillSetup s).program = s.program := by
  simp only [fillSetup, block_program]

@[simp] theorem fillSetup_error (s : ArmState) : read_err (fillSetup s) = read_err s := by
  simp only [fillSetup, block_error]

theorem fillResult_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 228#64) : run 5 s = fillResult s := by
  have follows : Follows base fillResultOps s := by
    change r .PC s = _ at pc
    simp [Follows, fillResultOps, Op.row, Op.effect, load, store, put, next, compare,
      state_simp_rules, aligned, pc, BitVec.add_assoc]
  rw [fillResult]
  exact runs fillResultOps s base code error follows

theorem fillResult_pc (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 228#64) :
    read_pc (fillResult s) =
      if (read_mem_bytes 8 (r (.GPR 31#5) s + 96#64) s + r (.GPR 23#5) s).toNat < 64
      then base + 364#64 else base + 248#64 := by
  let total := read_mem_bytes 8 (r (.GPR 31#5) s + 96#64) s + r (.GPR 23#5) s
  have totalDef : total =
      read_mem_bytes 8 (r (.GPR 31#5) s + 96#64) s + r (.GPR 23#5) s := rfl
  have lower : (AddWithCarry total (~~~64#64) 1#1).2.c = 1#1 ↔ 64 ≤ total.toNat :=
    Udivti3.cmp_carry total 64#64
  change r .PC s = _ at pc
  by_cases enough : 64 ≤ total.toNat
  · have carry := lower.mpr enough
    rw [show ~~~64#64 = 18446744073709551551#64 by decide] at carry
    simp (config := {decide := true, instances := true})
      [fillResult, fillResultOps, block, Op.effect, load, store, put, next, compare,
        branch, state_simp_rules, pc, BitVec.add_assoc, ← totalDef, carry,
        show ¬total.toNat < 64 by omega]
  · have carry : (AddWithCarry total (~~~64#64) 1#1).2.c ≠ 1#1 := by
      intro h
      exact enough (lower.mp h)
    rw [show ~~~64#64 = 18446744073709551551#64 by decide] at carry
    simp (config := {decide := true, instances := true})
      [fillResult, fillResultOps, block, Op.effect, load, store, put, next, compare,
        branch, state_simp_rules, pc, BitVec.add_assoc, ← totalDef, carry,
        show total.toNat < 64 by omega]

theorem bufferedSetup_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 248#64) : run 4 s = bufferedSetup s := by
  have follows : Follows base bufferedSetupOps s := by
    change r .PC s = _ at pc
    simp [Follows, bufferedSetupOps, Op.row, Op.effect, put, next,
      state_simp_rules, aligned, pc, BitVec.add_assoc]
  rw [bufferedSetup]
  exact runs bufferedSetupOps s base code error follows

theorem bufferedSetup_arguments (s : ArmState) :
    r (.GPR 0#5) (bufferedSetup s) = r (.GPR 24#5) s + 64#64 ∧
    r (.GPR 1#5) (bufferedSetup s) = r (.GPR 31#5) s ∧
    r (.GPR 21#5) (bufferedSetup s) = r (.GPR 21#5) s + r (.GPR 23#5) s ∧
    r (.GPR 20#5) (bufferedSetup s) = r (.GPR 20#5) s - r (.GPR 23#5) s := by
  simp [bufferedSetup, bufferedSetupOps, block, Op.effect, put, next, state_simp_rules]

end SszArm.Hash.Combine
