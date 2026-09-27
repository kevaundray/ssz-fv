import SszArm.NatAddRightTrim
import SszArm.NatAddInputs

namespace SszArm.NatAdd

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Entry-to-width execution for every physical Large left representation. -/
theorem left_large_count (s : ArmState) (base : BitVec 64) (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base)
    (input : NatCompare.Operand s (r (.GPR 1#5) s) (r (.GPR 2#5) s) words)
    (large : r (.GPR 1#5) s ≠ 0#64) :
    ∃ fuel t, run fuel s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 (sigWords words) ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 (sigWords words) ∧
      read_pc t = base + (if sigWords words = 0 then 92#64 else 64#64) := by
  obtain ⟨count, source, memory⟩ := input.large large
  let ops : List Op := [.p0, .p4, .p8]
  let u := block base ops s
  have hpc : r .PC s = base := hp
  have started : run 3 s = u := block_run base ops s hc he ha (by
    simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, large, BitVec.add_assoc])
  have frame : NatCompare.Frame s u := scan_frame base ops s (by decide)
  have upc : read_pc u = base + 12#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules,
      hpc, large, BitVec.add_assoc]
  have uptr : r (.GPR 8#5) u = r (.GPR 1#5) s - 8#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules]
  have ucount : r (.GPR 10#5) u = BitVec.ofNat 64 words.length := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, ← count]
  obtain ⟨fuel, t, executed, scanned, out, leftCount, countCopy, returned⟩ :=
    left_trim base (r (.GPR 1#5) s) words words.length u (Nat.le_refl _)
      (scan_code frame hc) (frame.error.trans he) (frame.aligned ha) upc uptr ucount
      (frame.source _ _ source) (frame.words _ _ source memory)
  refine ⟨3 + fuel, t, ?_, frame.trans scanned,
    out.trans (scan_zero base ops s (by decide)), leftCount, countCopy, returned⟩
  rw [run_plus, started, executed]

/-- Right count extraction retains the original payload and its last-index
copy in X9, which the zero-left normalization branch subsequently rescans. -/
theorem right_large_count (s : ArmState) (base : BitVec 64) (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 300#64)
    (input : NatCompare.Operand s (r (.GPR 3#5) s) (r (.GPR 4#5) s) words)
    (large : r (.GPR 3#5) s ≠ 0#64) :
    ∃ fuel t, run fuel s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 words.length - 1#64 ∧
      (sigWords words ≠ 0 → r (.GPR 10#5) t = BitVec.ofNat 64 (sigWords words - 1)) ∧
      read_pc t = base + (if sigWords words = 0 then 408#64 else 360#64) := by
  obtain ⟨count, source, memory⟩ := input.large large
  let ops : List Op := [.p300, .p304]
  let u := block base ops s
  have hpc : r .PC s = base + 300#64 := hp
  have started : run 2 s = u := block_run base ops s hc he ha (by
    simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, BitVec.add_assoc])
  have frame : NatCompare.Frame s u := scan_frame base ops s (by decide)
  have upc : read_pc u = base + 308#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  have ucount : r (.GPR 11#5) u = BitVec.ofNat 64 words.length - 1#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, ← count]
  obtain ⟨fuel, t, executed, scanned, out, leftCount, originalIndex, rightCount, returned⟩ :=
    right_trim base (r (.GPR 3#5) s) words words.length u (Nat.le_refl _)
      (scan_code frame hc) (frame.error.trans he) (frame.aligned ha) upc
      (frame.registers 3#5 (by decide)) ucount
      (frame.source _ _ source) (frame.words _ _ source memory)
  refine ⟨2 + fuel, t, ?_, frame.trans scanned,
    out.trans (scan_zero base ops s (by decide)), ?_, ?_, rightCount, returned⟩
  · rw [run_plus, started, executed]
  · simpa [u, ops, block, Op.effect, put, next, state_simp_rules] using leftCount
  · simpa [u, ops, block, Op.effect, put, next, state_simp_rules, ← count] using originalIndex

def smallLargeOps (word : BitVec 64) : List Op :=
  [.p0, .p72] ++ if word = 0#64 then [.p292, .p296] else [.p76, .p80, .p84]

/-- The immediate left path joins the same arbitrary right scan. -/
theorem small_large_start (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base)
    (small : r (.GPR 1#5) s = 0#64) (large : r (.GPR 3#5) s ≠ 0#64) :
    ∃ fuel t, run fuel s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 (sigWords [r (.GPR 2#5) s]) ∧
      read_pc t = base + 300#64 := by
  let ops := smallLargeOps (r (.GPR 2#5) s)
  let t := block base ops s
  have hpc : r .PC s = base := hp
  have follow : Follows base ops s := by
    by_cases zero : r (.GPR 2#5) s = 0#64 <;>
      simp [ops, smallLargeOps, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hpc, small, large, zero, BitVec.add_assoc]
  refine ⟨ops.length, t, block_run base ops s hc he ha follow,
    scan_frame base ops s ?_, scan_zero base ops s ?_, ?_, ?_⟩
  · dsimp only [ops, smallLargeOps]; split <;> decide
  · dsimp only [ops, smallLargeOps]; split <;> decide
  all_goals
    by_cases zero : r (.GPR 2#5) s = 0#64 <;>
      simp [t, ops, smallLargeOps, block, Op.effect, put, next,
        state_simp_rules, hpc, small, large, zero, sigWords, significantCount]

end SszArm.NatAdd
