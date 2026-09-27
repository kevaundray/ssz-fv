import SszArm.NatDivisionCopyRound

namespace SszArm.NatDivision

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem copy_round_frame (s : ArmState) (base destination word : BitVec 64) (i count : Nat)
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 i)
    (h24 : r (.GPR 24#5) s = destination)
    (hi : i < count) (hsp : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hd : CopyDestination s destination count) :
    CopyFrame destination count s (copyRoundResult s base word) := by
  have haddr : (destination + BitVec.ofNat 64 (8 * i)).toNat = destination.toNat + 8 * i := by
    have := hd.1
    bv_omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [copyRoundResult, copyStoreResult, scanLoadResult, NatCompare.saved, state_simp_rules]
  · simp [copyRoundResult, copyStoreResult, copyTailOps, copyGuardOps,
      scanLoadResult, block, Op.effect, put, next, NatCompare.saved, state_simp_rules]
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [copyRoundResult, copyStoreResult, copyTailOps,
      copyGuardOps, scanLoadResult, block, Op.effect, put, next, NatCompare.saved, state_simp_rules]
  · intro reg
    simp [copyRoundResult, copyStoreResult, copyTailOps, copyGuardOps,
      scanLoadResult, block, Op.effect, put, next, NatCompare.saved, state_simp_rules]
  · intro a hslot hout
    rw [copy_round_memory s base destination word i h9 h24]
    unfold copyRoundMemory
    rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ a
      (by rw [haddr]; have := hd.1; omega)
      (by rw [haddr]; omega)]
    rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ a (by bv_omega) (by bv_omega)]
    exact (NatCompare.saved_frame s 11#5 hsp).memory a hslot

/-- Every earlier copied word survives both lowering saves and the next word
store; the newly copied word is observed in all eight of its bytes. -/
theorem copy_round_copied (s : ArmState) (base destination : BitVec 64)
    (words : List (BitVec 64)) (i count : Nat)
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 i)
    (h24 : r (.GPR 24#5) s = destination)
    (hi : i < count) (hsp : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hd : CopyDestination s destination count) (copied : Copied s destination words i) :
    Copied (copyRoundResult s base (words[i]?.getD 0#64)) destination words (i + 1) := by
  intro j hj
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp
    (copy_round_memory s base destination (words[i]?.getD 0#64) i h9 h24)) 8 _]
  have hiaddr : (destination + BitVec.ofNat 64 (8 * i)).toNat = destination.toNat + 8 * i := by
    have := hd.1
    bv_omega
  have hjaddr : (destination + BitVec.ofNat 64 (8 * j)).toNat = destination.toNat + 8 * j := by
    have := hd.1
    bv_omega
  by_cases heq : j = i
  · subst j
    unfold copyRoundMemory
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _
      (by rw [hiaddr]; have := hd.1; omega)
  · have hji : j < i := by omega
    unfold copyRoundMemory
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by rw [hjaddr]; have := hd.1; omega)
      (by rw [hiaddr]; have := hd.1; omega)
      (by rw [hjaddr, hiaddr]; omega)]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by rw [hjaddr]; have := hd.1; omega) (by bv_omega)
      (by rw [hjaddr]; have := hd.2; bv_omega)]
    unfold NatCompare.saved
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      (by rw [hjaddr]; have := hd.1; omega) (by bv_omega)
      (by rw [hjaddr]; have := hd.2; bv_omega)]
    exact copied j hji

end SszArm.NatDivision
