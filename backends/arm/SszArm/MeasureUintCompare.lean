import SszArm.MeasureUintWidthFrame

namespace SszArm.Measure.Uint

def pairValue (low high : BitVec 64) : Nat := low.toNat + 2^64 * high.toNat

theorem pair_compare_carry (leftLow leftHigh rightLow rightHigh : BitVec 64) :
    (AddWithCarry leftHigh (~~~rightHigh)
      (AddWithCarry leftLow (~~~rightLow) 1#1).2.c).2.c = 1#1 ↔
    pairValue rightLow rightHigh ≤ pairValue leftLow leftHigh := by
  have carry : (AddWithCarry leftLow (~~~rightLow) 1#1).2.c =
      if rightLow.toNat ≤ leftLow.toNat then 1#1 else 0#1 := by
    by_cases ordered : rightLow.toNat ≤ leftLow.toNat
    · simpa [ordered] using (Udivti3.cmp_carry leftLow rightLow).2 ordered
    · have absent : (AddWithCarry leftLow (~~~rightLow) 1#1).2.c ≠ 1#1 := by
        intro present
        exact ordered ((Udivti3.cmp_carry leftLow rightLow).1 present)
      simp only [ordered, ↓reduceIte]
      bv_omega
  rw [carry, Udivti3.adc_carry]
  have ll := leftLow.isLt
  have lh := leftHigh.isLt
  have rl := rightLow.isLt
  have rh := rightHigh.isLt
  unfold pairValue Udivti3.radix
  split <;> simp only [BitVec.toNat_not, BitVec.toNat_ofNat] <;> omega

def finalCompareOps : List WidthOp := [.p3912, .p3916, .p3920]

/-- The original CMP/SBCS/B.HS unsigned 128-bit comparison, including equality.
The untouched X21/X20 pair remains the original descriptor representation. -/
theorem final_compare (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3912#64) :
    let t := widthBlock base finalCompareOps s
    run 3 s = t ∧ NatNarrow.Frame s t ∧ t.mem = s.mem ∧
      read_pc t = if pairValue (r (.GPR 8#5) s) (r (.GPR 9#5) s) ≤
          pairValue (r (.GPR 10#5) s) (r (.GPR 11#5) s)
        then base + 4144#64 else base + 3924#64 := by
  have pc' : r .PC s = base + 3912#64 := pc
  have follows : WidthFollows base finalCompareOps s := by
    simp [finalCompareOps, WidthFollows, WidthOp.row, WidthOp.effect, compare64, next,
      Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules, pc', BitVec.add_assoc]
  refine ⟨width_run base finalCompareOps s code error aligned follows,
    width_pure_frame base _ s (by decide), ?_, ?_⟩
  · simp [finalCompareOps, widthBlock, WidthOp.effect, compare64, next,
      Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules]
  · simp [finalCompareOps, widthBlock, WidthOp.effect, compare64, next,
      Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules, pair_compare_carry]

end SszArm.Measure.Uint
