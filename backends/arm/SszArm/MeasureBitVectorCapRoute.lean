import SszArm.MeasureBitVectorCapRead

namespace SszArm.Measure.BitVector

open Result

private theorem cap_route588_effect (s : ArmState) :
    p588.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 13#5) (r (.GPR 10#5) s - 1#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 1, S := 0, sh := 0, imm12 := 1, Rn := 10, Rd := 13 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem cap_route2828_effect (s : ArmState) :
    p2828.effect s = w .PC
      (if r (.GPR 10#5) s = 0#64 then r .PC s + 436#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Compare_branch { sf := 1, op := 0, imm19 := 109, Rt := 10 })) s = _
  by_cases empty : r (.GPR 10#5) s = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, empty]

private theorem cap_route3264_effect (s : ArmState) :
    p3264.effect s = w .PC (r .PC s + 4#64) (w (.GPR 11#5) 0#64 s) := by
  exact cap_read2992_effect s

@[irreducible] def scanStartResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 592#64) (w (.GPR 13#5) (r (.GPR 10#5) s - 1#64) s)

theorem scan_start_run (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (error : read_err s = .None) (pc : read_pc s = base + 588#64) :
    run 1 s = scanStartResult s base := by
  have follows : Follows base [p588] s := ⟨error, pc, trivial⟩
  rw [show 1 = [p588].length by rfl, runs _ s base code follows]
  change r .PC s = _ at pc
  simp [scanStartResult, effect, cap_route588_effect, pc, BitVec.add_assoc]

theorem scan_start_frame (s : ArmState) (base : BitVec 64) : CapFrame s (scanStartResult s base) := by
  constructor
  · simp [scanStartResult, state_simp_rules]
  · simp [scanStartResult, state_simp_rules]
  · intro reg outside
    have different : reg ≠ 13#5 := fun equal => outside (by simp [equal])
    simp [scanStartResult, state_simp_rules, different]
  · intro reg
    simp [scanStartResult, state_simp_rules]
  · intro address outside
    simp [scanStartResult, state_simp_rules]

def zeroOps (empty : Bool) : List Op := if empty then [p2828, p3264] else [p2828]

@[irreducible] def zeroResult (s : ArmState) (base : BitVec 64) : ArmState :=
  if r (.GPR 10#5) s = 0#64 then w .PC (base + 3268#64) (w (.GPR 11#5) 0#64 s)
    else w .PC (base + 2832#64) s

theorem zero_run (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (error : read_err s = .None) (pc : read_pc s = base + 2828#64) :
    run (zeroOps (decide (r (.GPR 10#5) s = 0#64))).length s = zeroResult s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base (zeroOps (decide (r (.GPR 10#5) s = 0#64))) s := by
    by_cases empty : r (.GPR 10#5) s = 0#64 <;>
      simp (config := {decide := true, instances := true})
        [zeroOps, Follows, show p2828.offset = 2828 from rfl,
         show p3264.offset = 3264 from rfl, cap_route2828_effect,
         state_simp_rules, pc, error, empty, BitVec.add_assoc]
  rw [runs _ s base code follows]
  by_cases empty : r (.GPR 10#5) s = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [zeroResult, zeroOps, effect, cap_route2828_effect, cap_route3264_effect,
       state_simp_rules, pc, empty, BitVec.add_assoc, NatExact.gpr_w_pc]

theorem zero_frame (s : ArmState) (base : BitVec 64) : CapFrame s (zeroResult s base) := by
  by_cases empty : r (.GPR 10#5) s = 0#64
  all_goals
    constructor
    · simp [zeroResult, empty, state_simp_rules]
    · simp [zeroResult, empty, state_simp_rules]
    · intro reg outside
      have different : reg ≠ 11#5 := fun equal => outside (by simp [equal])
      simp_all [zeroResult, state_simp_rules]
    · intro reg
      simp [zeroResult, empty, state_simp_rules]
    · intro address outside
      simp [zeroResult, empty, state_simp_rules]

end SszArm.Measure.BitVector
