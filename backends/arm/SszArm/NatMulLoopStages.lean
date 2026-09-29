import SszArm.NatMulLoopControl

namespace SszArm.NatMul

abbrev loopInnerChanged : List (BitVec 5) := [0#5, 1#5, 15#5, 16#5, 17#5, 18#5]
abbrev loopOuterChanged : List (BitVec 5) :=
  [0#5, 1#5, 11#5, 12#5, 13#5, 14#5, 15#5, 16#5, 17#5, 18#5]

private theorem stage_vectors (base : BitVec 64) (ops : List Op)
    (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (block base ops s) = r (.SFP reg) s := by
  exact NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (r (.SFP reg)) ops s (fun op _ t => op.sfp base t reg)

theorem loop_guard_stable (base : BitVec 64) (s : ArmState) :
    LoopStable loopInnerChanged s (block base [.p680, .p684, .p688] s) := by
  constructor
  · simp
  · simp
  · simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  · intro reg different
    simp_all [block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  · intro reg
    exact stage_vectors base _ s reg

theorem loop_load_stable (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64) :
    LoopStable loopInnerChanged s (loopLoaded site s base value) := by
  refine ⟨loop_loaded_program _ _ _ _, loop_loaded_error _ _ _ _,
    loop_loaded_stack _ _ _ _, ?_, loop_loaded_vectors _ _ _ _⟩
  intro reg different
  apply loop_loaded_registers
  cases site <;> simp_all [LoopLoadSite.destination]

theorem loop_product_stable (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    LoopStable loopInnerChanged s (highProductCompleted s base) := by
  have bound : 48 ≤ (r (.GPR 31#5) (Op.p756.effect base s)).toNat := by
    simpa [Op.effect, put, next, state_simp_rules] using stack
  constructor
  · simp [highProductCompleted, high_completed_program]
  · simp [highProductCompleted, high_completed_error]
  · simp [highProductCompleted, high_completed_stack, Op.effect, put, next, state_simp_rules]
  · intro reg different
    rw [highProductCompleted, high_completed_registers _ base bound reg (by simp_all)]
    simp_all [Op.effect, put, next, state_simp_rules]
  · intro reg
    simp [highProductCompleted, high_completed_vectors]

theorem loop_product_frame (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48)] s
      (highProductCompleted s base) := by
  have bound : 48 ≤ (r (.GPR 31#5) (Op.p756.effect base s)).toNat := by
    simpa [Op.effect, put, next, state_simp_rules] using stack
  have frame := high_completed_frame (Op.p756.effect base s) base bound
  have sameStack : r (.GPR 31#5) (Op.p756.effect base s) = r (.GPR 31#5) s := by
    simp [Op.effect, put, next, state_simp_rules]
  intro address outside
  have preserved := frame address (by
    simpa only [sameStack] using outside)
  exact preserved.trans (by simp [Op.effect, put, next, state_simp_rules])

theorem loop_product_pc (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 756#64) :
    read_pc (highProductCompleted s base) = base + 872#64 := by
  change r .PC s = base + 756#64 at pc
  rw [highProductCompleted, high_completed_pc]
  simp [Op.effect, put, next, state_simp_rules, pc, BitVec.add_assoc]

theorem loop_adds_stable (base : BitVec 64) (s : ArmState) :
    LoopStable loopInnerChanged s (loopAdds base s) := by
  constructor
  · simp [loopAdds]
  · simp [loopAdds]
  · simp [loopAdds, block, Op.effect, put, next, state_simp_rules]
  · intro reg different
    simp_all [loopAdds, block, Op.effect, put, next, state_simp_rules]
  · intro reg
    exact stage_vectors base _ s reg

theorem loop_store_stable (site : LoopStoreSite) (base : BitVec 64) (s : ArmState) :
    LoopStable loopInnerChanged s (loopStored site s base) :=
  ⟨loop_stored_program _ _ _, loop_stored_error _ _ _, loop_stored_registers _ _ _ _,
    fun reg _ => loop_stored_registers _ _ _ reg, loop_stored_vectors _ _ _⟩

theorem loop_carried_stable (base : BitVec 64) (s : ArmState) :
    LoopStable loopInnerChanged s (loopCarried base s) := by
  constructor <;> simp_all [loopCarried, state_simp_rules]

theorem loop_column_stable (base : BitVec 64) (s : ArmState) :
    LoopStable loopInnerChanged s (loopColumn base s) := by
  constructor
  · simp [loopColumn]
  · simp [loopColumn]
  · simp [loopColumn, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  · intro reg different
    simp_all [loopColumn, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  · intro reg
    exact stage_vectors base _ s reg

/-- Project before unfolding: only the four carry-chain inputs, its untouched
column counter, and the outgoing ADDS flag are relevant. -/
theorem loop_adds_values (s : ArmState) (base a b old carry : BitVec 64)
    (low : r (.GPR 0#5) s = a * b) (high : r (.GPR 18#5) s = NatMulProduct.high a b)
    (previous : r (.GPR 1#5) s = old) (incoming : r (.GPR 15#5) s = carry)
    (zero : r (.GPR 17#5) s = 0#64) :
    r (.GPR 18#5) (loopAdds base s) = (SszNative.LimbMul.step a b old carry.toNat).1 ∧
    (r (.GPR 17#5) (loopAdds base s) +
      if r (.FLAG .C) (loopAdds base s) = 1#1 then 1#64 else 0#64).toNat =
        (SszNative.LimbMul.step a b old carry.toNat).2 := by
  have lowValue : r (.GPR 18#5) (loopAdds base s) = a * b + carry + old := by
    simp only [loopAdds, block, List.foldl_cons, List.foldl_nil]
    simp [Op.effect, put, next, state_simp_rules, low, incoming, previous]
  have highValue : r (.GPR 17#5) (loopAdds base s) =
      NatMulProduct.high a b + NatMulProduct.carryWord (a * b) carry := by
    simp only [loopAdds, block, List.foldl_cons, List.foldl_nil]
    simp [Op.effect, put, next, state_simp_rules, low, high, incoming, zero,
      NatMulProduct.carryWord]
  have flagValue : r (.FLAG .C) (loopAdds base s) =
      (AddWithCarry (a * b + carry) old 0#1).2.c := by
    simp only [loopAdds, block, List.foldl_cons, List.foldl_nil]
    simp [Op.effect, put, next, state_simp_rules, low, incoming, previous]
  have arithmetic := NatMulProduct.step_eq_adc_carry_first a b old carry
  simp only [NatMulArithmetic.carry_result, BitVec.setWidth_zero, BitVec.add_zero] at arithmetic
  rw [lowValue, highValue, flagValue, ← NatMulProduct.carryWord_eq_cset]
  exact ⟨(congrArg Prod.fst arithmetic).symm, (congrArg Prod.snd arithmetic).symm⟩

end SszArm.NatMul
