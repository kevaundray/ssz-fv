import SszArm.NatMulWordRoundRun

namespace SszArm.NatMulWord

def roundAddress (s : ArmState) : BitVec 64 :=
  r (.GPR 15#5) s + (r (.GPR 13#5) s <<< 3)

theorem round_high_low (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    r (.GPR 18#5) (roundHigh s base) = r (.GPR 17#5) s * r (.GPR 3#5) s := by
  unfold roundHigh
  rw [high_completed_registers .loop _ _
    (by simpa [roundLow, Op.effect, put, next, state_simp_rules] using stack) _ (by decide)]
  simp [roundLow, Op.effect, put, next, state_simp_rules]

theorem round_high_high (s : ArmState) (base : BitVec 64) :
    r (.GPR 17#5) (roundHigh s base) =
      NatMulProduct.high (r (.GPR 17#5) s) (r (.GPR 3#5) s) := by
  unfold roundHigh
  rw [high_completed_value]
  simp [HighSite.left, roundLow, Op.effect, put, next, state_simp_rules]

theorem round_high_registers (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) (reg : BitVec 5)
    (high : reg ≠ 17#5) (low : reg ≠ 18#5) :
    r (.GPR reg) (roundHigh s base) = r (.GPR reg) s := by
  unfold roundHigh
  rw [high_completed_registers .loop _ _
    (by simpa [roundLow, Op.effect, put, next, state_simp_rules] using stack) _ high]
  simp [roundLow, Op.effect, put, next, state_simp_rules, low]

theorem round_added_low (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    r (.GPR 18#5) (roundAdded s base) =
      r (.GPR 17#5) s * r (.GPR 3#5) s + r (.GPR 14#5) s := by
  simp only [roundAdded, Op.effect, put, next, state_simp_rules]
  rw [round_high_low s base stack,
    round_high_registers s base stack 14#5 (by decide) (by decide)]

theorem round_added_high (s : ArmState) (base : BitVec 64) :
    r (.GPR 17#5) (roundAdded s base) =
      NatMulProduct.high (r (.GPR 17#5) s) (r (.GPR 3#5) s) := by
  simp [roundAdded, Op.effect, put, next, state_simp_rules, round_high_high]

theorem round_added_flag (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    r (.FLAG .C) (roundAdded s base) =
      (AddWithCarry (r (.GPR 17#5) s * r (.GPR 3#5) s) (r (.GPR 14#5) s) 0#1).2.c := by
  simp only [roundAdded, Op.effect, put, next, state_simp_rules]
  rw [round_high_low s base stack,
    round_high_registers s base stack 14#5 (by decide) (by decide)]

theorem round_added_registers (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) (reg : BitVec 5)
    (high : reg ≠ 17#5) (low : reg ≠ 18#5) :
    r (.GPR reg) (roundAdded s base) = r (.GPR reg) s := by
  simp only [roundAdded, Op.effect, put, next, state_simp_rules, low, ↓reduceIte]
  exact round_high_registers s base stack reg high low

theorem round_store_effect (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (roundAddress s).toNat + 8 ≤ 2^64)
    (separate : (roundAddress s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 48 ∨
      (r (.GPR 31#5) s).toNat ≤ (roundAddress s).toNat) :
    roundStored s base = w .PC (read_pc (roundAdded s base) + 32#64)
      (storeMemory (roundAdded s base)) := by
  have address : storeAddress (roundAdded s base) = roundAddress s := by
    unfold storeAddress roundAddress
    rw [round_added_registers s base stack 15#5 (by decide) (by decide),
      round_added_registers s base stack 13#5 (by decide) (by decide)]
  have sp := round_added_registers s base stack 31#5 (by decide) (by decide)
  exact store_effect (roundAdded s base) base (by rw [sp]; omega)
    (by rw [address]; exact physical) (by rw [address, sp]; omega)

theorem round_completed_step (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (roundAddress s).toNat + 8 ≤ 2^64)
    (separate : (roundAddress s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 48 ∨
      (r (.GPR 31#5) s).toNat ≤ (roundAddress s).toNat) :
    (r (.GPR 18#5) (roundCompleted s base), (r (.GPR 14#5) (roundCompleted s base)).toNat) =
      SszNative.LimbMul.step (r (.GPR 3#5) s) (r (.GPR 17#5) s) 0#64
        (r (.GPR 14#5) s).toNat := by
  have stored := round_store_effect s base stack physical separate
  rw [word_step]
  apply Prod.ext
  · rw [roundCompleted, round_tail_registers _ _ 18#5 (by decide) (by decide), stored]
    simpa only [storeMemory, NatCompare.saved, state_simp_rules] using round_added_low s base stack
  · rw [roundCompleted, round_tail_carry, stored]
    simp only [storeMemory, NatCompare.saved, state_simp_rules]
    rw [round_added_high, round_added_flag s base stack]

theorem round_completed_registers (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (roundAddress s).toNat + 8 ≤ 2^64)
    (separate : (roundAddress s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 48 ∨
      (r (.GPR 31#5) s).toNat ≤ (roundAddress s).toNat)
    (reg : BitVec 5) (index : reg ≠ 13#5) (carry : reg ≠ 14#5)
    (high : reg ≠ 17#5) (low : reg ≠ 18#5) :
    r (.GPR reg) (roundCompleted s base) = r (.GPR reg) s := by
  rw [roundCompleted, round_tail_registers _ _ reg index carry,
    round_store_effect s base stack physical separate]
  simpa only [storeMemory, NatCompare.saved, state_simp_rules] using
    round_added_registers s base stack reg high low

end SszArm.NatMulWord
