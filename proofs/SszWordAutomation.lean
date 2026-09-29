import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide

namespace SszNative.WordAutomation

/-- Close machine-word obligations using kernel-checked arithmetic or the
standard bitvector normalization lemmas. No SAT solver, native decision
checker, additional axioms, or changes to proof limits are involved. -/
macro "ssz_word" : tactic =>
  `(tactic| first
    | exact BitVec.sub_add_cancel _ _
    | exact BitVec.add_sub_cancel _ _
    | omega
    | (simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
        BitVec.toNat_setWidth] at *; omega)
    | (bv_normalize; done))

end SszNative.WordAutomation
