import SszArm.NatMulHighFrame

namespace SszArm.NatMul

def highProductCompleted (s : ArmState) (base : BitVec 64) : ArmState :=
  highCompleted (Op.p756.effect base s) base

theorem high_product_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 756#64) :
    run 29 s = highProductCompleted s base := by
  let t := Op.p756.effect base s
  have tCode : CodeAt t base := by simpa only [t, CodeAt, Op.program] using code
  have tError : read_err t = .None := (Op.error _ _ _).trans error
  have tAligned : CheckSPAlignment t := Op.aligned _ _ _ aligned
  have tPC : read_pc t = base + 760#64 := by
    have pcRead : r .PC s = base + 756#64 := pc
    simp [t, Op.effect, put, next, state_simp_rules, pcRead, BitVec.add_assoc]
  change run (28 + 1) s = _
  rw [run, step s base .p756 code pc error aligned,
    high_run t base tCode tError tAligned tPC]
  rfl

theorem high_product_values (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    r (.GPR 0#5) (highProductCompleted s base) = r (.GPR 18#5) s * r (.GPR 14#5) s ∧
    r (.GPR 18#5) (highProductCompleted s base) =
      NatMulProduct.high (r (.GPR 18#5) s) (r (.GPR 14#5) s) := by
  have tStack : 48 ≤ (r (.GPR 31#5) (Op.p756.effect base s)).toNat := by
    simpa [Op.effect, put, next, state_simp_rules] using stack
  constructor
  · rw [highProductCompleted, high_completed_registers _ base tStack 0#5 (by decide)]
    simp [Op.effect, put, next, state_simp_rules]
  · rw [highProductCompleted, high_completed_value]
    simp [Op.effect, put, next, state_simp_rules]

theorem high_product_value (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    (r (.GPR 0#5) (highProductCompleted s base)).toNat +
      2^64 * (r (.GPR 18#5) (highProductCompleted s base)).toNat =
        (r (.GPR 18#5) s).toNat * (r (.GPR 14#5) s).toNat := by
  rw [(high_product_values s base stack).1, (high_product_values s base stack).2]
  exact NatMulProduct.product_value _ _

end SszArm.NatMul
