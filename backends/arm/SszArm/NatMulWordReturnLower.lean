import SszArm.NatMulWordReturnLowerSteps

namespace SszArm.NatMulWord

open NatFromU128 (scratchPair scratchPair_reads store_field_write)


theorem pair_finish (kind : PairKind) (s : ArmState) (owned : ReturnOwned s) :
    pairRestore (pairStore kind (pairEnter s)) =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * kind.ops.length))
        (scratchPair s (r (.GPR 31#5) s) (r (.GPR 0#5) s)
          (r (.GPR 9#5) s) (r (.GPR 10#5) s) (kind.low s) (kind.high s)) := by
  obtain ⟨stack, output, separate⟩ := owned
  have reads := scratchPair_reads s (r (.GPR 31#5) s) (r (.GPR 0#5) s)
    (r (.GPR 9#5) s) (r (.GPR 10#5) s) (kind.low s) (kind.high s) stack (by omega) (by omega)
  simp [scratchPair, BitVec.sub_eq_add_neg, BitVec.add_assoc] at reads
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases kind <;> cases f <;>
      simp (config := {decide := true, instances := true})
        [pairRestore, pairStore, pairEnter, scratchPair, PairKind.ops, PairKind.enterOps,
         PairKind.storeOps, PairKind.restoreOps, PairKind.low, PairKind.high,
         state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg, store_field_write] at reads ⊢
    all_goals
      simp (config := {decide := true, instances := true})
        [state_simp_rules, reads.1, reads.2]
    all_goals
      rename_i reg
      by_cases h9 : reg = 9#5
      · subst reg; simp [state_simp_rules]
      · by_cases h10 : reg = 10#5
        · subst reg; simp [state_simp_rules]
        · by_cases h31 : reg = 31#5
          · subst reg; simp [state_simp_rules]
          · simp (disch := simp_all) [state_simp_rules]
  · cases kind <;>
      simp [pairRestore, pairStore, pairEnter, scratchPair, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    cases kind <;>
      simp [pairRestore, pairStore, pairEnter, scratchPair, PairKind.low, PairKind.high,
        state_simp_rules, ArmState.mem_w_eq_mem, store_field_write]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem pair_effect (kind : PairKind) (s : ArmState) (base : BitVec 64) (owned : ReturnOwned s) :
    block base kind.ops s =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * kind.ops.length))
        (scratchPair s (r (.GPR 31#5) s) (r (.GPR 0#5) s)
          (r (.GPR 9#5) s) (r (.GPR 10#5) s) (kind.low s) (kind.high s)) := by
  have append (xs ys : List Op) (t : ArmState) :
      block base (xs ++ ys) t = block base ys (block base xs t) := by
    simp only [block, List.foldl_append]
  rw [PairKind.ops, append, append, pair_enter_effect, pair_store_effect, pair_restore_effect]
  exact pair_finish kind s owned

theorem zero_pair_effect (s : ArmState) (base : BitVec 64) (owned : ReturnOwned s) :
    block base zeroPairOps s = w .PC (read_pc s + 44#64) (pairMemory s 0#64) :=
  pair_effect .zero s base owned

theorem small_pair_effect (s : ArmState) (base : BitVec 64) (owned : ReturnOwned s) :
    block base smallPairOps s = w .PC (read_pc s + 40#64) (pairMemory s (r (.GPR 8#5) s)) :=
  pair_effect .small s base owned

end SszArm.NatMulWord
