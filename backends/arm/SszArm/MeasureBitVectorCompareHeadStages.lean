import SszArm.MeasureBitVectorCompareInstructions

namespace SszArm.Measure.BitVector

open Result

/-- Flag algebra is proved before instantiating the arithmetic comparison. -/
private theorem compareHead_flags_pc (s : ArmState) (flags : PState) (nextPC : BitVec 64) :
    write_pstate flags (w .PC nextPC s) = w .PC nextPC (write_pstate flags s) := by
  simp only [write_pstate, w, write_base_pc, write_base_flag]

private theorem compareHead_store_flags (s : ArmState) (flags : PState)
    (address data : BitVec 64) :
    write_mem_bytes 8 address data (write_pstate flags s) =
      write_pstate flags (write_mem_bytes 8 address data s) := by
  simp only [write_pstate, NatExact.store_w]

@[irreducible] def compareHeadMarked (s : ArmState) (base : BitVec 64) (flags : PState) : ArmState :=
  w .PC (base + 3272#64) (write_pstate flags s)

@[irreducible] def compareHeadLowered (s : ArmState) (base : BitVec 64) (flags : PState) : ArmState :=
  w .PC (base + 3276#64)
    (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) (write_pstate flags s))

@[irreducible] def compareHeadSpilled (s : ArmState) (base : BitVec 64) (flags : PState) : ArmState :=
  w .PC (base + 3280#64)
    (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) (write_pstate flags (NatCompare.saved s 9#5)))

theorem compareHeadMarked_compare (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 3268#64) :
    p3268.effect s = compareHeadMarked s base
      (AddWithCarry (r (.GPR 11#5) s) (~~~r (.GPR 9#5) s) 1#1).2 := by
  change r .PC s = _ at pc
  rw [compare3268_effect, compareHead_flags_pc, pc]
  have nextPC : base + 3268#64 + 4#64 = base + 3272#64 := by bv_omega
  rw [nextPC]
  simp only [compareHeadMarked]

private theorem compareHeadMarked_pc (s : ArmState) (base : BitVec 64) (flags : PState) :
    r .PC (compareHeadMarked s base flags) = base + 3272#64 := by
  simp only [compareHeadMarked, r_of_w_same]

private theorem compareHeadMarked_sp (s : ArmState) (base : BitVec 64) (flags : PState) :
    r (.GPR 31#5) (compareHeadMarked s base flags) = r (.GPR 31#5) s := by
  simp [compareHeadMarked, state_simp_rules]

private theorem compareHeadLowered_pc (s : ArmState) (base : BitVec 64) (flags : PState) :
    r .PC (compareHeadLowered s base flags) = base + 3276#64 := by
  simp only [compareHeadLowered, r_of_w_same]

private theorem compareHeadLowered_sp (s : ArmState) (base : BitVec 64) (flags : PState) :
    r (.GPR 31#5) (compareHeadLowered s base flags) = r (.GPR 31#5) s - 16#64 := by
  simp (disch := decide) only [compareHeadLowered, r_of_w_different, r_of_w_same]

private theorem compareHeadLowered_nine (s : ArmState) (base : BitVec 64) (flags : PState) :
    r (.GPR 9#5) (compareHeadLowered s base flags) = r (.GPR 9#5) s := by
  simp (config := {decide := true}) [compareHeadLowered, state_simp_rules]

private theorem compareHeadSpilled_pc (s : ArmState) (base : BitVec 64) (flags : PState) :
    r .PC (compareHeadSpilled s base flags) = base + 3280#64 := by
  simp only [compareHeadSpilled, r_of_w_same]

private theorem compareHeadSpilled_zero (s : ArmState) (base : BitVec 64) (flags : PState) :
    r (.FLAG .Z) (compareHeadSpilled s base flags) = flags.z := by
  simp [compareHeadSpilled, NatCompare.saved, state_simp_rules]

private theorem compareHeadMarked_lower (s : ArmState) (base : BitVec 64) (flags : PState) :
    p3272.effect (compareHeadMarked s base flags) = compareHeadLowered s base flags := by
  rw [compare3272_effect, compareHeadMarked_pc, compareHeadMarked_sp]
  have nextPC : base + 3272#64 + 4#64 = base + 3276#64 := by bv_omega
  rw [nextPC]
  simp only [compareHeadMarked, compareHeadLowered, NatExact.gpr_w_pc, w_of_w_shadow]

private theorem compareHeadLowered_spill (s : ArmState) (base : BitVec 64) (flags : PState)
    (aligned : CheckSPAlignment s) :
    p3276.effect (compareHeadLowered s base flags) = compareHeadSpilled s base flags := by
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have ready : CheckSPAlignment (compareHeadLowered s base flags) := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, compareHeadLowered_sp] using lower
  rw [compare3276_effect _ ready, compareHeadLowered_pc, compareHeadLowered_sp, compareHeadLowered_nine]
  have nextPC : base + 3276#64 + 4#64 = base + 3280#64 := by bv_omega
  rw [nextPC]
  simp only [compareHeadLowered, compareHeadSpilled, NatCompare.saved,
    NatExact.store_w, compareHead_store_flags, w_of_w_shadow]

private theorem compareHeadSpilled_branch (s : ArmState) (base : BitVec 64) (flags : PState) :
    p3280.effect (compareHeadSpilled s base flags) =
      w .PC (if flags.z = 1#1 then base + 3296#64 else base + 3284#64)
        (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64)
          (write_pstate flags (NatCompare.saved s 9#5))) := by
  rw [compare3280_effect, compareHeadSpilled_zero, compareHeadSpilled_pc]
  have taken : base + 3280#64 + 16#64 = base + 3296#64 := by bv_omega
  have nextPC : base + 3280#64 + 4#64 = base + 3284#64 := by bv_omega
  rw [taken, nextPC]
  unfold compareHeadSpilled
  exact w_of_w_shadow

private theorem compare_three_effects (first second third : Op)
    (s t u v : ArmState) (firstEffect : first.effect s = t)
    (secondEffect : second.effect t = u) (thirdEffect : third.effect u = v) :
    effect [first, second, third] s = v := by
  change third.effect (second.effect (first.effect s)) = v
  exact (congrArg (fun state => third.effect (second.effect state)) firstEffect).trans
    ((congrArg third.effect secondEffect).trans thirdEffect)

theorem compareHeadMarked_remainder (s : ArmState) (base : BitVec 64) (flags : PState)
    (aligned : CheckSPAlignment s) :
    effect [p3272, p3276, p3280] (compareHeadMarked s base flags) =
      w .PC (if flags.z = 1#1 then base + 3296#64 else base + 3284#64)
        (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64)
          (write_pstate flags (NatCompare.saved s 9#5))) := by
  exact compare_three_effects p3272 p3276 p3280
    (compareHeadMarked s base flags) (compareHeadLowered s base flags)
    (compareHeadSpilled s base flags) _
    (compareHeadMarked_lower s base flags)
    (compareHeadLowered_spill s base flags aligned)
    (compareHeadSpilled_branch s base flags)

end SszArm.Measure.BitVector
