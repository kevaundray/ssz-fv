import SszArm.NatMulArithmetic

namespace SszArm.NatMulStateFold

theorem preserves {α β γ : Type} (step : β → α → β) (observe : β → γ)
    (ops : List α) (s : β)
    (each : ∀ op ∈ ops, ∀ t, observe (step t op) = observe t) :
    observe (ops.foldl step s) = observe s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    exact (induction _ (by intro next member; exact each next (by simp [member]))).trans
      (each op (by simp) s)

theorem advancing {α : Type} (step : ArmState → α → ArmState)
    (ops : List α) (s : ArmState)
    (each : ∀ op ∈ ops, ∀ t, read_pc (step t op) = read_pc t + 4#64) :
    read_pc (ops.foldl step s) = read_pc s + BitVec.ofNat 64 (4 * ops.length) := by
  induction ops generalizing s with
  | nil => simp
  | cons op ops induction =>
    rw [List.foldl_cons, induction _ (by intro next member; exact each next (by simp [member])),
      each op (by simp) s]
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
    bv_omega

end SszArm.NatMulStateFold
