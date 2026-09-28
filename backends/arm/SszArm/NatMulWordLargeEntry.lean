import SszArm.NatMulWordLargeMemory

namespace SszArm.NatMulWord.Large

open UintCodec (widthLoad)

/-- The scanner's XOR implements minus-eight independently of the raw extent. -/
theorem trim_bias (words : List (BitVec 64)) : trimBias words = -8#64 := by
  have bytes : BitVec.ofNat 64 (8 * words.length) = BitVec.ofNat 64 words.length <<< 3 := by bv_omega
  have mask : 18446744073709551608#64 = BitVec.allOnes 64 <<< 3 := by decide
  rw [trimBias, bytes, mask, ← BitVec.shiftLeft_xor_distrib, BitVec.xor_allOnes,
    ← BitVec.shiftLeft_add_distrib, BitVec.not_eq_neg_add]
  have cancel : (-BitVec.ofNat 64 words.length - 1#64) + BitVec.ofNat 64 words.length = -1#64 := by bv_omega
  rw [cancel]
  decide

theorem trim_bias_count (words : List (BitVec 64)) (count : Nat) (positive : 0 < count) :
    trimBias words - BitVec.ofNat 64 (8 * (count - 1)) = -BitVec.ofNat 64 (8 * count) := by
  rw [trim_bias]
  have countEq : 8 * (count - 1) + 8 = 8 * count := by omega
  rw [← countEq, BitVec.ofNat_add]
  bv_omega

theorem scan_arena {s t : ArmState} {operand : SszNative.NatOperand} {factor : BitVec 64}
    (owned : Owned s operand factor) (priorFrame : SmallFrame s t) : arenaOf t = arenaOf s := by
  have address := priorFrame.header owned 0 (by decide)
  have capacity := priorFrame.header owned 8 (by decide)
  have used := priorFrame.header owned 16 (by decide)
  simp only [BitVec.ofNat_zero, BitVec.add_zero] at address
  simp only [arenaOf, address, capacity, used]

theorem scan_outcome {s t : ArmState} {operand : SszNative.NatOperand} {factor : BitVec 64}
    (owned : Owned s operand factor) (priorFrame : SmallFrame s t) :
    outcome t operand factor = outcome s operand factor := by
  simp only [outcome, scan_arena owned priorFrame]

theorem scan_writes {s t : ArmState} {operand : SszNative.NatOperand} {factor : BitVec 64}
    (owned : Owned s operand factor) (priorFrame : SmallFrame s t) :
    writesFor t (outcome t operand factor) = writesFor s (outcome s operand factor) := by
  simp only [scan_outcome owned priorFrame, writesFor, localWrites, priorFrame.sp, priorFrame.out, priorFrame.arena]

theorem scan_owned {s t : ArmState} {operand : SszNative.NatOperand} {factor : BitVec 64}
    (owned : Owned s operand factor) (priorFrame : SmallFrame s t)
    (pointer : r (.GPR 1#5) t = operand.pointer)
    (payload : r (.GPR 2#5) t = operand.payload) : Owned t operand factor := by
  have model := scan_outcome owned priorFrame
  have arena := scan_arena owned priorFrame
  have writes := scan_writes owned priorFrame
  refine ⟨pointer, payload, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (priorFrame.registers 3#5 (by decide)).trans owned.factorRegister
  · exact NatAdd.operand_at_preserved (priorFrame.full (outcome s operand factor)) operand
      owned.operandAt owned.inputOwned
  · simpa only [priorFrame.out] using owned.outputBound
  · simpa only [priorFrame.sp] using owned.stackBound
  · simpa only [priorFrame.sp, priorFrame.out] using owned.outputStack
  · simpa only [priorFrame.arena] using owned.arenaBound
  · simpa only [arena] using owned.arenaStorage
  · simpa only [arena] using owned.arenaNonnull
  · simpa only [model, localWrites, priorFrame.sp, priorFrame.out, priorFrame.arena] using owned.arenaLocal
  · intro reservation allocated
    rw [model] at allocated
    simpa only [model, localWrites, priorFrame.sp, priorFrame.out, priorFrame.arena] using owned.fresh reservation allocated
  · simpa only [writes] using owned.inputOwned

theorem scan_post {s u t : ArmState} {operand : SszNative.NatOperand} {factor : BitVec 64}
    (owned : Owned s operand factor) (priorFrame : SmallFrame s u) (post : Post u t operand factor) :
    Post s t operand factor := by
  have model := scan_outcome owned priorFrame
  have writes := scan_writes owned priorFrame
  have frame : Delimited.MemoryFrame (writesFor s (outcome s operand factor)) s t :=
    (priorFrame.full (outcome s operand factor)).trans (by simpa only [writes] using post.frame)
  refine ⟨priorFrame.returned post.returned, ?_, ?_, ?_, frame,
    NatAdd.operand_preserved frame operand owned.operandAt owned.inputOwned, ?_, ?_⟩
  · simpa only [priorFrame.out, model] using post.result
  · simpa only [model] using post.written
  · simpa only [priorFrame.arena, model] using post.cursor
  · have initial := priorFrame.header owned 0 (by decide)
    simp only [BitVec.ofNat_zero, BitVec.add_zero] at initial
    simpa only [priorFrame.arena] using post.arenaBase.trans initial
  · have initial := priorFrame.header owned 8 (by decide)
    simpa only [priorFrame.arena] using post.arenaCapacity.trans initial

end SszArm.NatMulWord.Large
