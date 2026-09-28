import SszArm.MeasureBitsWidthLowSteps

namespace SszArm.Measure.Bits.Width

open Result

def lowOps : List Op := [p1852, p1856, p1860, p1864, p1868, p1872]

@[irreducible] def lowResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 1876#64)
    (w (.GPR 8#5) (quotientLow (r (.GPR 26#5) s) (r (.GPR 25#5) s))
      (NatCompare.saved s 9#5))

theorem low_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1852#64) (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    run 6 s = lowResult s base := by
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (NatCompare.saved s 9#5) =
      r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base lowOps s := by
    simp (config := {decide := true, instances := true})
      [Follows, lowOps, low1852_effect, low1856_effect, low1860_effect,
        low1864_effect, low1868_effect, low1872_effect,
        CheckSPAlignment, state_simp_rules, bitvec_rules, lower, error, pc,
        NatExact.store_w, BitVec.add_assoc, BitVec.sub_add_cancel]
    all_goals simp [p1852, p1856, p1860, p1864, p1868, p1872]
  rw [show 6 = lowOps.length by rfl, runs _ s base code follows]
  simp only [NatCompare.saved] at restored
  simp (config := {decide := true, instances := true})
    [effect, lowOps, low1852_effect, low1856_effect, low1860_effect,
      low1864_effect, low1868_effect, low1872_effect,
      CheckSPAlignment, state_simp_rules, bitvec_rules, lower, pc,
      NatExact.store_w, NatExact.gpr_w_pc, BitVec.add_assoc, BitVec.sub_add_cancel]
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases r8 : reg = 8#5
      · subst reg
        simp (config := {decide := true, instances := true})
          [lowResult, quotientLow, NatCompare.saved, state_simp_rules, restored]
      · by_cases r9 : reg = 9#5
        · subst reg
          simp (config := {decide := true, instances := true})
            [lowResult, quotientLow, NatCompare.saved, state_simp_rules, restored]
        · by_cases rsp : reg = 31#5
          · subst reg
            simp (config := {decide := true, instances := true})
              [lowResult, quotientLow, NatCompare.saved, state_simp_rules, restored]
          · simp (config := {decide := true, instances := true})
              [lowResult, quotientLow, NatCompare.saved, state_simp_rules,
                r8, r9, rsp, restored]
    | PC | SFP _ | FLAG _ | ERR =>
      simp [lowResult, NatCompare.saved, state_simp_rules]
  · simp [lowResult, NatCompare.saved, state_simp_rules]
  · intro n address
    simp [lowResult, NatCompare.saved, state_simp_rules]

end SszArm.Measure.Bits.Width
