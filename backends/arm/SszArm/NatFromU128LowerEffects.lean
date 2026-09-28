import SszArm.NatFromU128LowerCongruence

namespace SszArm.NatFromU128

theorem lower_smallPair_effect (s : ArmState) (base : BitVec 64) (space : Space s) :
    block base LowerKind.smallPair.ops s =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * LowerKind.smallPair.ops.length))
        (lowerMemory .smallPair s) := by
  obtain ⟨stack, output, separate⟩ := space
  have reads := scratchPair_reads s (r (.GPR 31#5) s)
    (r (.GPR 0#5) s + 0#64) (r (.GPR 9#5) s) (r (.GPR 10#5) s)
    (0#64) (r (.GPR 2#5) s) stack (by bv_omega) (by bv_omega)
  simp [scratchPair, BitVec.sub_eq_add_neg] at reads
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f <;>
      simp (config := {decide := true, instances := true})
        [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
         LowerKind.offset, state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg,
         store_field_write, reads.1, reads.2]
    all_goals
      rename_i reg
      by_cases h9 : reg = 9#5
      · subst reg; simp (config := {decide := true}) [state_simp_rules]
      · by_cases h10 : reg = 10#5
        · subst reg; simp (config := {decide := true}) [state_simp_rules]
        · by_cases h31 : reg = 31#5
          · subst reg; simp (config := {decide := true}) [state_simp_rules]
          · simp (disch := simp_all) [state_simp_rules]
  · simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules, ArmState.mem_w_eq_mem,
      store_field_write, BitVec.add_assoc, BitVec.sub_eq_add_neg]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem lower_smallStatus_effect (s : ArmState) (base : BitVec 64) (space : Space s) :
    block base LowerKind.smallStatus.ops s =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * LowerKind.smallStatus.ops.length))
        (lowerMemory .smallStatus s) := by
  obtain ⟨stack, output, separate⟩ := space
  have reads := scratchStatus_reads s (r (.GPR 31#5) s)
    (r (.GPR 0#5) s + 64#64) (r (.GPR 9#5) s) (r (.GPR 10#5) s)
    stack (by bv_omega) (by bv_omega)
  simp [scratchStatus, BitVec.sub_eq_add_neg] at reads
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f <;>
      simp (config := {decide := true, instances := true})
        [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
         LowerKind.offset, state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg,
         store_field_write, reads.1, reads.2]
    all_goals
      rename_i reg
      by_cases h9 : reg = 9#5
      · subst reg; simp (config := {decide := true}) [state_simp_rules]
      · by_cases h10 : reg = 10#5
        · subst reg; simp (config := {decide := true}) [state_simp_rules]
        · by_cases h31 : reg = 31#5
          · subst reg; simp (config := {decide := true}) [state_simp_rules]
          · simp (disch := simp_all) [state_simp_rules]
  · simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules, ArmState.mem_w_eq_mem,
      store_field_write, BitVec.add_assoc, BitVec.sub_eq_add_neg]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem lower_wideStatus_effect (s : ArmState) (base : BitVec 64) (space : Space s) :
    block base LowerKind.wideStatus.ops s =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * LowerKind.wideStatus.ops.length))
        (lowerMemory .wideStatus s) := by
  obtain ⟨stack, output, separate⟩ := space
  have reads := scratchStatus_reads s (r (.GPR 31#5) s)
    (r (.GPR 0#5) s + 64#64) (r (.GPR 9#5) s) (r (.GPR 10#5) s)
    stack (by bv_omega) (by bv_omega)
  simp [scratchStatus, BitVec.sub_eq_add_neg] at reads
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f <;>
      simp (config := {decide := true, instances := true})
        [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
         LowerKind.offset, state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg,
         store_field_write, reads.1, reads.2]
    all_goals
      rename_i reg
      by_cases h9 : reg = 9#5
      · subst reg; simp (config := {decide := true}) [state_simp_rules]
      · by_cases h10 : reg = 10#5
        · subst reg; simp (config := {decide := true}) [state_simp_rules]
        · by_cases h31 : reg = 31#5
          · subst reg; simp (config := {decide := true}) [state_simp_rules]
          · simp (disch := simp_all) [state_simp_rules]
  · simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules, ArmState.mem_w_eq_mem,
      store_field_write, BitVec.add_assoc, BitVec.sub_eq_add_neg]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem lower_zero48_effect (s : ArmState) (base : BitVec 64) (space : Space s) :
    block base LowerKind.zero48.ops s =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * LowerKind.zero48.ops.length))
        (lowerMemory .zero48 s) := by
  obtain ⟨stack, output, separate⟩ := space
  have reads := scratchPair_reads s (r (.GPR 31#5) s)
    (r (.GPR 0#5) s + 48#64) (r (.GPR 9#5) s) (r (.GPR 10#5) s)
    (0#64) (0#64) stack (by bv_omega) (by bv_omega)
  simp [scratchPair, BitVec.sub_eq_add_neg, BitVec.add_assoc] at reads
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f <;>
      simp (config := {decide := true, instances := true})
        [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
         LowerKind.offset, state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg,
         store_field_write, reads.1, reads.2]
    all_goals
      rename_i reg
      by_cases h9 : reg = 9#5
      · subst reg; simp (config := {decide := true}) [state_simp_rules]
      · by_cases h10 : reg = 10#5
        · subst reg; simp (config := {decide := true}) [state_simp_rules]
        · by_cases h31 : reg = 31#5
          · subst reg; simp (config := {decide := true}) [state_simp_rules]
          · simp (disch := simp_all) [state_simp_rules]
  · simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules, ArmState.mem_w_eq_mem,
      store_field_write, BitVec.add_assoc, BitVec.sub_eq_add_neg]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem lower_zero32_effect (s : ArmState) (base : BitVec 64) (space : Space s) :
    block base LowerKind.zero32.ops s =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * LowerKind.zero32.ops.length))
        (lowerMemory .zero32 s) := by
  obtain ⟨stack, output, separate⟩ := space
  have reads := scratchPair_reads s (r (.GPR 31#5) s)
    (r (.GPR 0#5) s + 32#64) (r (.GPR 9#5) s) (r (.GPR 10#5) s)
    (0#64) (0#64) stack (by bv_omega) (by bv_omega)
  simp [scratchPair, BitVec.sub_eq_add_neg, BitVec.add_assoc] at reads
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f <;>
      simp (config := {decide := true, instances := true})
        [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
         LowerKind.offset, state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg,
         store_field_write, reads.1, reads.2]
    all_goals
      rename_i reg
      by_cases h9 : reg = 9#5
      · subst reg; simp (config := {decide := true}) [state_simp_rules]
      · by_cases h10 : reg = 10#5
        · subst reg; simp (config := {decide := true}) [state_simp_rules]
        · by_cases h31 : reg = 31#5
          · subst reg; simp (config := {decide := true}) [state_simp_rules]
          · simp (disch := simp_all) [state_simp_rules]
  · simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules, ArmState.mem_w_eq_mem,
      store_field_write, BitVec.add_assoc, BitVec.sub_eq_add_neg]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem lower_zero16_effect (s : ArmState) (base : BitVec 64) (space : Space s) :
    block base LowerKind.zero16.ops s =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * LowerKind.zero16.ops.length))
        (lowerMemory .zero16 s) := by
  obtain ⟨stack, output, separate⟩ := space
  have reads := scratchPair_reads s (r (.GPR 31#5) s)
    (r (.GPR 0#5) s + 16#64) (r (.GPR 9#5) s) (r (.GPR 10#5) s)
    (0#64) (0#64) stack (by bv_omega) (by bv_omega)
  simp [scratchPair, BitVec.sub_eq_add_neg, BitVec.add_assoc] at reads
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f <;>
      simp (config := {decide := true, instances := true})
        [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
         LowerKind.offset, state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg,
         store_field_write, reads.1, reads.2]
    all_goals
      rename_i reg
      by_cases h9 : reg = 9#5
      · subst reg; simp (config := {decide := true}) [state_simp_rules]
      · by_cases h10 : reg = 10#5
        · subst reg; simp (config := {decide := true}) [state_simp_rules]
        · by_cases h31 : reg = 31#5
          · subst reg; simp (config := {decide := true}) [state_simp_rules]
          · simp (disch := simp_all) [state_simp_rules]
  · simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules, ArmState.mem_w_eq_mem,
      store_field_write, BitVec.add_assoc, BitVec.sub_eq_add_neg]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem lower_errorPair_effect (s : ArmState) (base : BitVec 64) (space : Space s) :
    block base LowerKind.errorPair.ops s =
      w .PC (read_pc s + BitVec.ofNat 64 (4 * LowerKind.errorPair.ops.length))
        (lowerMemory .errorPair s) := by
  obtain ⟨stack, output, separate⟩ := space
  have reads := scratchPair_reads s (r (.GPR 31#5) s)
    (r (.GPR 0#5) s + 0#64) (r (.GPR 10#5) s) (r (.GPR 11#5) s)
    (r (.GPR 9#5) s) (0#64) stack (by bv_omega) (by bv_omega)
  simp [scratchPair, BitVec.sub_eq_add_neg] at reads
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f <;>
      simp (config := {decide := true, instances := true})
        [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
         LowerKind.offset, state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg,
         store_field_write, reads.1, reads.2]
    all_goals
      rename_i reg
      by_cases h10 : reg = 10#5
      · subst reg; simp (config := {decide := true}) [state_simp_rules]
      · by_cases h11 : reg = 11#5
        · subst reg; simp (config := {decide := true}) [state_simp_rules]
        · by_cases h31 : reg = 31#5
          · subst reg; simp (config := {decide := true}) [state_simp_rules]
          · simp (disch := simp_all) [state_simp_rules]
  · simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    simp [LowerKind.ops, block, Op.effect, put, next, lowerMemory, lowerSaved,
      LowerKind.offset, state_simp_rules, ArmState.mem_w_eq_mem,
      store_field_write, BitVec.add_assoc, BitVec.sub_eq_add_neg]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

end SszArm.NatFromU128
