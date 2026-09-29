import SszArm.HashFinalizeScalarStep

namespace SszArm.Hash.Finalize

/-- A symbolic GPR query is definitionally a different field from the PC. -/
@[state_simp_rules] theorem scalar_gpr_pc (s : ArmState) (reg : BitVec 5) (pc : BitVec 64) :
    r (.GPR reg) (w .PC pc s) = r (.GPR reg) s :=
  r_of_w_different (by intro equal; cases equal)

/-- NZCV updates never require case analysis on the queried GPR number. -/
@[state_simp_rules] theorem scalar_gpr_flag (s : ArmState) (reg : BitVec 5)
    (flag : PFlag) (value : BitVec 1) :
    r (.GPR reg) (w (.FLAG flag) value s) = r (.GPR reg) s :=
  r_of_w_different (by intro equal; cases equal)

/-- Observe a branch result without splitting either complete machine state. -/
@[state_simp_rules] theorem scalar_read_ite (field : StateField) (condition : Prop)
    [Decidable condition] (yes no : ArmState) :
    r field (if condition then yes else no) =
      if condition then r field yes else r field no := by
  split <;> rfl

end SszArm.Hash.Finalize
