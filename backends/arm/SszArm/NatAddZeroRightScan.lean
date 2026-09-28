import SszArm.NatAddZeroTerminal

namespace SszArm.NatAdd

open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- A zero left significant count still executes the real right count scan and
then rescans the original right representation before returning its normalization. -/
theorem zero_left_large_right (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (left : SszNative.NatOperand)
    (owned : Owned s left (.large pointer words))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 300#64) (zero : left.wordCount = 0)
    (count : r (.GPR 8#5) s = 0#64) :
    ∃ fuel t, run fuel s = t ∧ Post s t left (.large pointer words) := by
  have nonzero : r (.GPR 3#5) s ≠ 0#64 := by
    rw [owned.rightPointer]
    change pointer ≠ 0#64
    have positive := owned.rightAt.1
    intro h
    simp [h, SszNative.NatOperand.pointer] at positive
  obtain ⟨fuel, u, execution, scanned, out, retained, originalIndex, rightCount, pc⟩ :=
    right_large_count s base words hc he ha hp owned.operands.2 nonzero
  have ownedU := owned.transport scanned out
  have countU : r (.GPR 8#5) u = 0#64 := retained.trans count
  let ops : List Op := if sigWords words = 0 then [.p408, .p412] else [.p360]
  let v := block base ops u
  have hpc : r .PC u = base + (if sigWords words = 0 then 408#64 else 360#64) := pc
  have ran : run ops.length u = v := by
    apply block_run base ops u (scan_code scanned hc) (scanned.error.trans he) (scanned.aligned ha)
    by_cases empty : sigWords words = 0 <;>
      simp [ops, empty, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hpc, countU, BitVec.add_assoc]
  have frame : NatCompare.Frame u v := scan_frame base ops u (by
    dsimp only [ops]
    split <;> decide)
  have outV : r (.GPR 0#5) v = r (.GPR 0#5) u := scan_zero base ops u (by
    dsimp only [ops]
    split <;> decide)
  have pcV : read_pc v = base + 460#64 := by
    by_cases empty : sigWords words = 0 <;>
      simp [v, ops, empty, block, Op.effect, put, next,
        state_simp_rules, hpc, countU, BitVec.add_assoc]
  have indexV : r (.GPR 9#5) v = BitVec.ofNat 64 words.length - 1#64 := by
    by_cases empty : sigWords words = 0 <;>
      simpa [v, ops, empty, block, Op.effect, put, next, state_simp_rules] using originalIndex
  apply Post.prepend owned scanned out fuel execution
  apply Post.prepend ownedU frame outV ops.length ran
  exact zero_borrow_post true v base pointer words left (.large pointer words)
    (ownedU.transport frame outV) (scan_code frame (scan_code scanned hc))
    (frame.error.trans (scanned.error.trans he)) (frame.aligned (scanned.aligned ha)) pcV
    rfl indexV (SszNative.NatAdd.run_zero_left left (.large pointer words)
      (arenaOf v).base (arenaOf v).capacity (arenaOf v).used zero)

/-- A zero right Large follows the real +408 branch: an immediate left returns
directly, while a borrowed left is rescanned from its original payload. -/
theorem zero_right_large_right (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (left : SszNative.NatOperand)
    (owned : Owned s left (.large pointer words))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 300#64) (nonzero : left.wordCount ≠ 0)
    (zero : (SszNative.NatOperand.large pointer words).wordCount = 0)
    (count : r (.GPR 8#5) s = BitVec.ofNat 64 left.wordCount) :
    ∃ fuel t, run fuel s = t ∧ Post s t left (.large pointer words) := by
  have ptrNonzero : r (.GPR 3#5) s ≠ 0#64 := by
    rw [owned.rightPointer]
    change pointer ≠ 0#64
    have positive := owned.rightAt.1
    intro h
    simp [h] at positive
  have bound : left.wordCount < 2^64 :=
    Nat.lt_of_le_of_lt (sigWords_le_length left.words) owned.operands.1.length_bound
  have notZero : BitVec.ofNat 64 left.wordCount ≠ 0#64 := by bv_omega
  have zeroWords : sigWords words = 0 := zero
  obtain ⟨fuel, u, execution, scanned, out, retained, originalIndex, rightCount, pc⟩ :=
    right_large_count s base words hc he ha hp owned.operands.2 ptrNonzero
  have ownedU := owned.transport scanned out
  have countU : r (.GPR 8#5) u ≠ 0#64 := by rw [retained, count]; exact notZero
  have pcU : read_pc u = base + 408#64 := by simpa only [zeroWords, ↓reduceIte] using pc
  have hpc : r .PC u = base + 408#64 := pcU
  apply Post.prepend owned scanned out fuel execution
  cases left with
  | small word =>
    let ops : List Op := [.p408, .p576]
    let v := block base ops u
    have ptr : r (.GPR 1#5) u = 0#64 := ownedU.leftPointer
    have ran : run ops.length u = v := block_run base ops u
      (scan_code scanned hc) (scanned.error.trans he) (scanned.aligned ha) (by
        simp [ops, Follows, Op.row, Op.effect, state_simp_rules, hpc, countU])
    have frame : NatCompare.Frame u v := scan_frame base ops u (by decide)
    have outV : r (.GPR 0#5) v = r (.GPR 0#5) u := scan_zero base ops u (by decide)
    have ownedV := ownedU.transport frame outV
    have pcV : read_pc v = base + 656#64 := by
      simp [v, ops, block, Op.effect, put, next, state_simp_rules, countU, ptr]
    apply Post.prepend ownedU frame outV ops.length ran
    apply zero_small_post .left v base word (.small word) (.large pointer words) ownedV
      (scan_code frame (scan_code scanned hc)) (frame.error.trans (scanned.error.trans he))
      (frame.aligned (scanned.aligned ha)) pcV ownedV.leftPointer ownedV.leftPayload
    simpa only [outcome, small_normalized] using SszNative.NatAdd.run_zero_right (.small word)
      (.large pointer words) (arenaOf v).base (arenaOf v).capacity (arenaOf v).used nonzero zero
  | large leftPointer leftWords =>
    let ops : List Op := [.p408, .p576, .p580]
    let v := block base ops u
    have ptr : r (.GPR 1#5) u ≠ 0#64 := by
      rw [ownedU.leftPointer]
      change leftPointer ≠ 0#64
      have positive := ownedU.leftAt.1
      intro h
      simp [h, SszNative.NatOperand.pointer] at positive
    have ran : run ops.length u = v := block_run base ops u
      (scan_code scanned hc) (scanned.error.trans he) (scanned.aligned ha) (by
        simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
          hpc, countU, ptr, BitVec.add_assoc])
    have frame : NatCompare.Frame u v := scan_frame base ops u (by decide)
    have outV : r (.GPR 0#5) v = r (.GPR 0#5) u := scan_zero base ops u (by decide)
    have pcV : read_pc v = base + 584#64 := by
      simp [v, ops, block, Op.effect, put, next, state_simp_rules, hpc, countU, ptr, BitVec.add_assoc]
    have indexV : r (.GPR 9#5) v = BitVec.ofNat 64 leftWords.length - 1#64 := by
      simp [v, ops, block, Op.effect, put, next, state_simp_rules, ownedU.leftPayload,
        SszNative.NatOperand.payload]
    apply Post.prepend ownedU frame outV ops.length ran
    exact zero_borrow_post false v base leftPointer leftWords (.large leftPointer leftWords)
      (.large pointer words) (ownedU.transport frame outV)
      (scan_code frame (scan_code scanned hc)) (frame.error.trans (scanned.error.trans he))
      (frame.aligned (scanned.aligned ha)) pcV rfl indexV
      (SszNative.NatAdd.run_zero_right (.large leftPointer leftWords) (.large pointer words)
        (arenaOf v).base (arenaOf v).capacity (arenaOf v).used nonzero zero)

end SszArm.NatAdd
