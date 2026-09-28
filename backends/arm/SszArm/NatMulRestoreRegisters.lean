import SszArm.NatMulRestoreOps

namespace SszArm.NatMul

theorem restore_register_19 (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    r (.GPR 19#5) (restored path s base) = r (.GPR 19#5) entry := by
  have observed := saved.words 19#5 88 (by decide)
  cases path <;>
    simp (config := {decide := true}) [restored, RestorePath.ops, block, Op.effect,
      put, next, state_simp_rules, observed, BitVec.add_assoc,
      show 80#64 + 8#64 = 88#64 by decide]

theorem restore_register_20 (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    r (.GPR 20#5) (restored path s base) = r (.GPR 20#5) entry := by
  have observed := saved.words 20#5 80 (by decide)
  cases path <;>
    simp (config := {decide := true}) [restored, RestorePath.ops, block, Op.effect,
      put, next, state_simp_rules, observed]

theorem restore_register_21 (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    r (.GPR 21#5) (restored path s base) = r (.GPR 21#5) entry := by
  have observed := saved.words 21#5 72 (by decide)
  cases path <;>
    simp (config := {decide := true}) [restored, RestorePath.ops, block, Op.effect,
      put, next, state_simp_rules, observed, BitVec.add_assoc,
      show 64#64 + 8#64 = 72#64 by decide]

theorem restore_register_22 (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    r (.GPR 22#5) (restored path s base) = r (.GPR 22#5) entry := by
  have observed := saved.words 22#5 64 (by decide)
  cases path <;>
    simp (config := {decide := true}) [restored, RestorePath.ops, block, Op.effect,
      put, next, state_simp_rules, observed]

theorem restore_register_23 (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    r (.GPR 23#5) (restored path s base) = r (.GPR 23#5) entry := by
  have observed := saved.words 23#5 56 (by decide)
  cases path <;>
    simp (config := {decide := true}) [restored, RestorePath.ops, block, Op.effect,
      put, next, state_simp_rules, observed, BitVec.add_assoc,
      show 48#64 + 8#64 = 56#64 by decide]

theorem restore_register_24 (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    r (.GPR 24#5) (restored path s base) = r (.GPR 24#5) entry := by
  have observed := saved.words 24#5 48 (by decide)
  cases path <;>
    simp (config := {decide := true}) [restored, RestorePath.ops, block, Op.effect,
      put, next, state_simp_rules, observed]

theorem restore_register_25 (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    r (.GPR 25#5) (restored path s base) = r (.GPR 25#5) entry := by
  have observed := saved.words 25#5 40 (by decide)
  cases path <;>
    simp (config := {decide := true}) [restored, RestorePath.ops, block, Op.effect,
      put, next, state_simp_rules, observed, BitVec.add_assoc,
      show 32#64 + 8#64 = 40#64 by decide]

theorem restore_register_26 (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    r (.GPR 26#5) (restored path s base) = r (.GPR 26#5) entry := by
  have observed := saved.words 26#5 32 (by decide)
  cases path <;>
    simp (config := {decide := true}) [restored, RestorePath.ops, block, Op.effect,
      put, next, state_simp_rules, observed]

theorem restore_register_27 (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    r (.GPR 27#5) (restored path s base) = r (.GPR 27#5) entry := by
  have observed := saved.words 27#5 24 (by decide)
  cases path <;>
    simp (config := {decide := true}) [restored, RestorePath.ops, block, Op.effect,
      put, next, state_simp_rules, observed, BitVec.add_assoc,
      show 16#64 + 8#64 = 24#64 by decide]

theorem restore_register_28 (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    r (.GPR 28#5) (restored path s base) = r (.GPR 28#5) entry := by
  have observed := saved.words 28#5 16 (by decide)
  cases path <;>
    simp (config := {decide := true}) [restored, RestorePath.ops, block, Op.effect,
      put, next, state_simp_rules, observed]

theorem restore_register_29 (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    r (.GPR 29#5) (restored path s base) = r (.GPR 29#5) entry := by
  have observed := saved.x29
  cases path <;>
    simp (config := {decide := true}) [restored, RestorePath.ops, block, Op.effect,
      put, next, state_simp_rules, observed]

theorem restore_register_30 (path : RestorePath) (entry s : ArmState) (base : BitVec 64)
    (saved : Saved entry s) :
    r (.GPR 30#5) (restored path s base) = r (.GPR 30#5) entry := by
  have observed := saved.words 30#5 0 (by decide)
  simp only [BitVec.add_zero] at observed
  cases path <;>
    simp (config := {decide := true}) [restored, RestorePath.ops, block, Op.effect,
      put, next, state_simp_rules, observed]

theorem restore_argument_0 (path : RestorePath) (s : ArmState) (base : BitVec 64) :
    r (.GPR 0#5) (restored path s base) = r (.GPR 0#5) s := by
  cases path <;>
    simp [restored, RestorePath.ops, block, Op.effect, put, next, state_simp_rules]

theorem restore_argument_1 (path : RestorePath) (s : ArmState) (base : BitVec 64) :
    r (.GPR 1#5) (restored path s base) = r (.GPR 1#5) s := by
  cases path <;>
    simp [restored, RestorePath.ops, block, Op.effect, put, next, state_simp_rules]

theorem restore_argument_2 (path : RestorePath) (s : ArmState) (base : BitVec 64) :
    r (.GPR 2#5) (restored path s base) = r (.GPR 2#5) s := by
  cases path <;>
    simp [restored, RestorePath.ops, block, Op.effect, put, next, state_simp_rules]

theorem restore_argument_3 (path : RestorePath) (s : ArmState) (base : BitVec 64) :
    r (.GPR 3#5) (restored path s base) = r (.GPR 3#5) s := by
  cases path <;>
    simp [restored, RestorePath.ops, block, Op.effect, put, next, state_simp_rules]

theorem restore_tail_argument_4 (s : ArmState) (base : BitVec 64) :
    r (.GPR 4#5) (restored .tail s base) = r (.GPR 5#5) s := by
  simp [restored, RestorePath.ops, block, Op.effect, put, next, state_simp_rules]

end SszArm.NatMul
