import SszArm.NatMulWordHighStages
import SszArm.NatFromU128LowerCongruence

namespace SszArm.NatMulWord

theorem high_save_first (s : ArmState) (base : BitVec 64) :
    block base HighSite.first.saveOps s =
      w (.GPR 31#5) (r (.GPR 31#5) s - 48#64)
        (w .PC (read_pc s + 28#64) (HighSite.first.spilled s)) := by
  simp [HighSite.saveOps, HighSite.spilled, HighSite.saved, block, Op.effect, put, next,
    NatMulSpill.six, state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg,
    NatFromU128.store_field_write]
  rw [w_of_w_commute (fld1 := .PC) (fld2 := .GPR 31#5) (by decide)]
  simp only [state_simp_rules]

theorem high_save_loop (s : ArmState) (base : BitVec 64) :
    block base HighSite.loop.saveOps s =
      w (.GPR 31#5) (r (.GPR 31#5) s - 48#64)
        (w .PC (read_pc s + 28#64) (HighSite.loop.spilled s)) := by
  simp [HighSite.saveOps, HighSite.spilled, HighSite.saved, block, Op.effect, put, next,
    NatMulSpill.six, state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg,
    NatFromU128.store_field_write]
  rw [w_of_w_commute (fld1 := .PC) (fld2 := .GPR 31#5) (by decide)]
  simp only [state_simp_rules]

theorem high_save_small (s : ArmState) (base : BitVec 64) :
    block base HighSite.small.saveOps s =
      w (.GPR 31#5) (r (.GPR 31#5) s - 48#64)
        (w .PC (read_pc s + 28#64) (HighSite.small.spilled s)) := by
  simp [HighSite.saveOps, HighSite.spilled, HighSite.saved, block, Op.effect, put, next,
    NatMulSpill.six, state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg,
    NatFromU128.store_field_write]
  rw [w_of_w_commute (fld1 := .PC) (fld2 := .GPR 31#5) (by decide)]
  simp only [state_simp_rules]

theorem high_save_effect (site : HighSite) (s : ArmState) (base : BitVec 64) :
    block base site.saveOps s =
      w (.GPR 31#5) (r (.GPR 31#5) s - 48#64)
        (w .PC (read_pc s + 28#64) (site.spilled s)) := by
  cases site with
  | first => exact high_save_first s base
  | loop => exact high_save_loop s base
  | small => exact high_save_small s base

end SszArm.NatMulWord
