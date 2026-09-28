import SszArm.NatMulHighOps

namespace SszArm.NatMul

theorem high_digits (s : ArmState) (base : BitVec 64) :
    r (.GPR 9#5) (block base highCore0 s) = ((r (.GPR 18#5) s).setWidth 32).setWidth 64 ∧
    r (.GPR 10#5) (block base highCore0 s) = r (.GPR 18#5) s >>> 32 ∧
    r (.GPR 11#5) (block base highCore0 s) = ((r (.GPR 14#5) s).setWidth 32).setWidth 64 ∧
    r (.GPR 12#5) (block base highCore0 s) = r (.GPR 14#5) s >>> 32 := by
  simp [highCore0, block, Op.effect, put, next, state_simp_rules]

theorem high_low_cross (s : ArmState) (base : BitVec 64) :
    r (.GPR 13#5) (block base highCore1 s) =
      r (.GPR 10#5) s * r (.GPR 11#5) s +
        ((r (.GPR 9#5) s * r (.GPR 11#5) s) >>> 32) := by
  rw [high_core1_word]
  exact NatMulWord.high_low_cross .first s base

theorem high_low_cross_preserved (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (different : reg ≠ 13#5) :
    r (.GPR reg) (block base highCore1 s) = r (.GPR reg) s := by
  rw [high_core1_word]
  exact NatMulWord.high_low_cross_preserved .first s base reg different

theorem high_high_cross (s : ArmState) (base : BitVec 64) :
    r (.GPR 11#5) (block base highCore2 s) = r (.GPR 13#5) s >>> 32 ∧
    r (.GPR 15#5) (block base highCore2 s) =
      (r (.GPR 9#5) s * r (.GPR 12#5) s +
        ((r (.GPR 13#5) s).setWidth 32).setWidth 64) >>> 32 := by
  rw [high_core2_word]
  exact NatMulWord.high_high_cross .first s base

theorem high_high_cross_preserved (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (notHigh : reg ≠ 11#5) (notCross : reg ≠ 15#5) :
    r (.GPR reg) (block base highCore2 s) = r (.GPR reg) s := by
  rw [high_core2_word]
  exact NatMulWord.high_high_cross_preserved .first s base reg notHigh notCross

theorem high_combine (s : ArmState) (base : BitVec 64) :
    r (.GPR 18#5) (block base highCore3 s) =
      r (.GPR 10#5) s * r (.GPR 12#5) s + r (.GPR 11#5) s + r (.GPR 15#5) s := by
  simp [highCore3, block, Op.effect, put, next, state_simp_rules,
    BitVec.add_comm, BitVec.add_assoc]

theorem high_core_value (s : ArmState) (base : BitVec 64) :
    r (.GPR 18#5) (block base highCoreOps s) =
      NatMulProduct.high (r (.GPR 18#5) s) (r (.GPR 14#5) s) := by
  let a := block base highCore0 s
  let b := block base highCore1 a
  have digit := high_digits s base
  have low := high_low_cross a base
  have upper := high_high_cross b base
  have a1b : r (.GPR 10#5) b = r (.GPR 10#5) a :=
    high_low_cross_preserved a base _ (by decide)
  have b1b : r (.GPR 12#5) b = r (.GPR 12#5) a :=
    high_low_cross_preserved a base _ (by decide)
  have a0b : r (.GPR 9#5) b = r (.GPR 9#5) a :=
    high_low_cross_preserved a base _ (by decide)
  rw [high_core_split, high_combine,
    high_high_cross_preserved b base 10#5 (by decide) (by decide),
    high_high_cross_preserved b base 12#5 (by decide) (by decide),
    upper.1, upper.2, a1b, b1b, a0b, low, digit.1, digit.2.1, digit.2.2.1, digit.2.2.2]
  rfl

end SszArm.NatMul
