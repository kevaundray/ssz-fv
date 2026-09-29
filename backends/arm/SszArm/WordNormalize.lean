import SszArm.NatExactState

open Lean.Parser.Tactic

namespace SszArm

/-- Canonicalize word literals and identity casts without unfolding register
files, arithmetic models, or instruction descriptors.  In particular, ordinary
numerals and `#` literals become the same `BitVec.ofNat` expression before a
rewrite or arithmetic proof observes them. -/
syntax "arm_word_nf" (location)? : tactic

macro_rules
  | `(tactic| arm_word_nf $[$loc:location]?) =>
    `(tactic| simp (config := { instances := true, failIfUnchanged := false }) only
      [BitVec.ofNat_eq_ofNat, BitVec.ofNatLT_eq_ofNat,
       BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat,
       BitVec.setWidth_eq, BitVec.cast_eq] $[$loc]?)

/-- Normalize a bounded register/memory summary algebraically.  Stores retain
order; PC writes move outward; projections never split the whole register file.
The caller chooses the instruction cut before invoking this tactic. -/
syntax "arm_state_nf" (location)? : tactic

macro_rules
  | `(tactic| arm_state_nf $[$loc:location]?) =>
    `(tactic| simp (config := { instances := true, failIfUnchanged := false })
      (disch := first | assumption | decide | contradiction) only
      [BitVec.ofNat_eq_ofNat, BitVec.ofNatLT_eq_ofNat,
       BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat,
       BitVec.setWidth_eq, BitVec.cast_eq,
       NatExact.store_w, NatExact.gpr_w_pc, NatExact.r_gpr_w,
       read_pc, read_err, r_of_w_same, r_of_w_different, w_of_w_shadow,
       r_of_write_mem_bytes, read_mem_bytes_of_w,
       ArmState.mem_w_eq_mem] $[$loc]?)

end SszArm
