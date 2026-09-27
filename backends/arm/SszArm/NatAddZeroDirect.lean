import SszArm.NatAddZeroRightScan

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def zeroLeftSmallOps (word : BitVec 64) : List Op :=
  if word = 0#64 then [.p92, .p96, .p572] else [.p92, .p96, .p100, .p104]

theorem zero_left_small_frame (s : ArmState) (base word : BitVec 64)
    (pointer : r (.GPR 3#5) s = 0#64) :
    NatCompare.Frame s (block base (zeroLeftSmallOps word) s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_, ?_⟩
  · intro reg outside
    by_cases h3 : reg = 3#5
    · subst reg
      by_cases zero : word = 0#64 <;>
        simp [zeroLeftSmallOps, zero, block, Op.effect, put, next, state_simp_rules, pointer]
    · by_cases zero : word = 0#64 <;>
        simp [zeroLeftSmallOps, zero, block, Op.effect, put, next, state_simp_rules, h3]
  · intro reg
    by_cases zero : word = 0#64 <;>
      simp [zeroLeftSmallOps, zero, block, Op.effect, put, next, state_simp_rules]
  · intro a outside
    by_cases zero : word = 0#64 <;>
      simp [zeroLeftSmallOps, zero, block, Op.effect, put, next, state_simp_rules]

/-- The zero-left Large branch reaches either the explicit zero descriptor or
the original immediate right descriptor, including the redundant MOV X3,#0. -/
theorem zero_left_large_small (s : ArmState) (base pointer word : BitVec 64)
    (words : List (BitVec 64)) (owned : Owned s (.large pointer words) (.small word))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 92#64)
    (zero : (SszNative.NatOperand.large pointer words).wordCount = 0)
    (count : r (.GPR 9#5) s = 0#64) :
    ∃ fuel t, run fuel s = t ∧ Post s t (.large pointer words) (.small word) := by
  let ops := zeroLeftSmallOps word
  let t := block base ops s
  have ptr : r (.GPR 3#5) s = 0#64 := owned.rightPointer
  have payload : r (.GPR 4#5) s = word := owned.rightPayload
  have hpc : r .PC s = base + 92#64 := hp
  have execution : run ops.length s = t := block_run base ops s hc he ha (by
    by_cases empty : word = 0#64 <;>
      simp [ops, zeroLeftSmallOps, empty, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hpc, ptr, payload, count, BitVec.add_assoc])
  have frame : NatCompare.Frame s t := zero_left_small_frame s base word ptr
  have out : r (.GPR 0#5) t = r (.GPR 0#5) s := by
    by_cases empty : word = 0#64 <;>
      simp [t, ops, zeroLeftSmallOps, empty, block, Op.effect, put, next, state_simp_rules]
  have ownedT := owned.transport frame out
  let path : StatusPath := if word = 0#64 then .zeroRight else .right
  have pc : read_pc t = base + BitVec.ofNat 64 (valueStart path) := by
    by_cases empty : word = 0#64 <;>
      simp [t, ops, path, zeroLeftSmallOps, valueStart, empty, block, Op.effect, put, next,
        state_simp_rules, hpc, ptr, payload, count, BitVec.add_assoc]
  apply Post.prepend owned frame out ops.length execution
  apply zero_small_post path t base word (.large pointer words) (.small word) ownedT
    (scan_code frame hc) (frame.error.trans he) (frame.aligned ha) pc
  · by_cases empty : word = 0#64 <;>
      simp [path, empty, valuePointer, ownedT.rightPointer, SszNative.NatOperand.pointer]
  · by_cases empty : word = 0#64 <;>
      simp [path, empty, valuePayload, ownedT.rightPayload, SszNative.NatOperand.payload]
  · simpa only [small_normalized] using SszNative.NatAdd.run_zero_left (.large pointer words)
      (.small word) (arenaOf t).base (arenaOf t).capacity (arenaOf t).used zero

/-- Immediate zero on the left takes the actual four-op entry path to STP+RET. -/
theorem zero_left_small_small (s : ArmState) (base word : BitVec 64)
    (owned : Owned s (.small 0#64) (.small word))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t (.small 0#64) (.small word) := by
  let ops : List Op := [.p0, .p72, .p292, .p296]
  let t := block base ops s
  have hpc : r .PC s = base := hp
  have r1 : r (.GPR 1#5) s = 0#64 := owned.leftPointer
  have r2 : r (.GPR 2#5) s = 0#64 := owned.leftPayload
  have r3 : r (.GPR 3#5) s = 0#64 := owned.rightPointer
  have execution : run ops.length s = t := block_run base ops s hc he ha (by
    simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, r1, r2, r3, BitVec.add_assoc])
  have frame : NatCompare.Frame s t := scan_frame base ops s (by decide)
  have out : r (.GPR 0#5) t = r (.GPR 0#5) s := scan_zero base ops s (by decide)
  have ownedT := owned.transport frame out
  have pc : read_pc t = base + 492#64 := by
    simp [t, ops, block, Op.effect, put, next, state_simp_rules, hpc, r1, r2, r3, BitVec.add_assoc]
  apply Post.prepend owned frame out ops.length execution
  apply zero_small_post .right t base word (.small 0#64) (.small word) ownedT
    (scan_code frame hc) (frame.error.trans he) (frame.aligned ha) pc
    ownedT.rightPointer ownedT.rightPayload
  simpa only [small_normalized] using SszNative.NatAdd.run_zero_left (.small 0#64)
    (.small word) (arenaOf t).base (arenaOf t).capacity (arenaOf t).used (by
      simp [SszNative.NatOperand.wordCount, SszNative.NatOperand.words,
        SszNative.Limbs.sigWords, SszNative.Limbs.significantCount])

def zeroRightSmallOps : List Op := [.p0, .p72, .p76, .p540, .p652]

theorem zero_right_small_frame (s : ArmState) (base : BitVec 64)
    (pointer : r (.GPR 1#5) s = 0#64) :
    NatCompare.Frame s (block base zeroRightSmallOps s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_, ?_⟩
  · intro reg outside
    by_cases h1 : reg = 1#5
    · subst reg
      simp [zeroRightSmallOps, block, Op.effect, put, next, state_simp_rules, pointer]
    · simp [zeroRightSmallOps, block, Op.effect, put, next, state_simp_rules, h1]
  · intro reg
    simp [zeroRightSmallOps, block, Op.effect, put, next, state_simp_rules]
  · intro a outside
    simp [zeroRightSmallOps, block, Op.effect, put, next, state_simp_rules]

/-- Immediate zero on the right returns the nonzero immediate left through the
real +540/+652 branch, without allocating or changing any arena word. -/
theorem zero_right_small_small (s : ArmState) (base word : BitVec 64)
    (owned : Owned s (.small word) (.small 0#64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (nonzero : (SszNative.NatOperand.small word).wordCount ≠ 0) :
    ∃ fuel t, run fuel s = t ∧ Post s t (.small word) (.small 0#64) := by
  have wordNonzero : word ≠ 0#64 := by
    intro h
    apply nonzero
    simp [h, SszNative.NatOperand.wordCount, SszNative.NatOperand.words,
      SszNative.Limbs.sigWords, SszNative.Limbs.significantCount]
  let t := block base zeroRightSmallOps s
  have hpc : r .PC s = base := hp
  have r1 : r (.GPR 1#5) s = 0#64 := owned.leftPointer
  have r2 : r (.GPR 2#5) s = word := owned.leftPayload
  have r3 : r (.GPR 3#5) s = 0#64 := owned.rightPointer
  have r4 : r (.GPR 4#5) s = 0#64 := owned.rightPayload
  have execution : run zeroRightSmallOps.length s = t := block_run base zeroRightSmallOps s hc he ha (by
    simp [zeroRightSmallOps, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, r1, r2, r3, r4, wordNonzero, BitVec.add_assoc])
  have frame : NatCompare.Frame s t := zero_right_small_frame s base r1
  have out : r (.GPR 0#5) t = r (.GPR 0#5) s := by
    simp [t, zeroRightSmallOps, block, Op.effect, put, next, state_simp_rules]
  have ownedT := owned.transport frame out
  have pc : read_pc t = base + 656#64 := by
    simp [t, zeroRightSmallOps, block, Op.effect, put, next, state_simp_rules,
      hpc, r1, r2, r3, r4, wordNonzero, BitVec.add_assoc]
  apply Post.prepend owned frame out zeroRightSmallOps.length execution
  apply zero_small_post .left t base word (.small word) (.small 0#64) ownedT
    (scan_code frame hc) (frame.error.trans he) (frame.aligned ha) pc
    ownedT.leftPointer ownedT.leftPayload
  simpa only [small_normalized] using SszNative.NatAdd.run_zero_right (.small word)
    (.small 0#64) (arenaOf t).base (arenaOf t).capacity (arenaOf t).used nonzero (by
      simp [SszNative.NatOperand.wordCount, SszNative.NatOperand.words,
        SszNative.Limbs.sigWords, SszNative.Limbs.significantCount])

end SszArm.NatAdd
