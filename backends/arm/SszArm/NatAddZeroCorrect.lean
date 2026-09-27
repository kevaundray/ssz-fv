import SszArm.NatAddZeroDirect

namespace SszArm.NatAdd

open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Every zero-left representation executes from the actual function entry to
RET. A Large right is counted and then normalized from its original full slice. -/
theorem zero_left_correct (s : ArmState) (base : BitVec 64)
    (left right : SszNative.NatOperand) (owned : Owned s left right)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (zero : left.wordCount = 0) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  cases left with
  | small word =>
    have wordZero := small_count_zero word zero
    subst word
    cases right with
    | small word => exact zero_left_small_small s base word owned hc he ha hp
    | large pointer words =>
      have ptr : r (.GPR 3#5) s ≠ 0#64 := by
        rw [owned.rightPointer]
        change pointer ≠ 0#64
        have positive := owned.rightAt.1
        intro h
        simp [h] at positive
      obtain ⟨fuel, u, ran, frame, out, count, pc⟩ :=
        small_large_start s base hc he ha hp owned.leftPointer ptr
      apply Post.prepend owned frame out fuel ran
      apply zero_left_large_right u base pointer words (.small 0#64)
        (owned.transport frame out) (scan_code frame hc) (frame.error.trans he)
        (frame.aligned ha) pc zero
      simpa [owned.leftPayload, SszNative.NatOperand.payload,
        sigWords, significantCount] using count
  | large pointer words =>
    have ptr : r (.GPR 1#5) s ≠ 0#64 := by
      rw [owned.leftPointer]
      change pointer ≠ 0#64
      have positive := owned.leftAt.1
      intro h
      simp [h] at positive
    have zeroWords : sigWords words = 0 := zero
    obtain ⟨fuel, u, ran, frame, out, count, copy, pc⟩ :=
      left_large_count s base words hc he ha hp owned.operands.1 ptr
    have ownedU := owned.transport frame out
    have pcU : read_pc u = base + 92#64 := by simpa only [zeroWords, ↓reduceIte] using pc
    have countU : r (.GPR 8#5) u = 0#64 := by simpa only [zeroWords] using count
    have copyU : r (.GPR 9#5) u = 0#64 := by simpa only [zeroWords] using copy
    apply Post.prepend owned frame out fuel ran
    cases right with
    | small word =>
      exact zero_left_large_small u base pointer word words ownedU (scan_code frame hc)
        (frame.error.trans he) (frame.aligned ha) pcU zero copyU
    | large rightPointer rightWords =>
      let ops : List Op := [.p92]
      let v := block base ops u
      have rightPtr : r (.GPR 3#5) u ≠ 0#64 := by
        rw [ownedU.rightPointer]
        change rightPointer ≠ 0#64
        have positive := ownedU.rightAt.1
        intro h
        simp [h] at positive
      have hpc : r .PC u = base + 92#64 := pcU
      have executed : run ops.length u = v := block_run base ops u
        (scan_code frame hc) (frame.error.trans he) (frame.aligned ha) (by
          simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, rightPtr])
      have second : NatCompare.Frame u v := scan_frame base ops u (by decide)
      have outV : r (.GPR 0#5) v = r (.GPR 0#5) u := scan_zero base ops u (by decide)
      have pcV : read_pc v = base + 300#64 := by
        simp [v, ops, block, Op.effect, put, next, state_simp_rules, rightPtr]
      have countV : r (.GPR 8#5) v = 0#64 := by
        simpa [v, ops, block, Op.effect, put, next, state_simp_rules] using countU
      apply Post.prepend ownedU second outV ops.length executed
      exact zero_left_large_right v base rightPointer rightWords (.large pointer words)
        (ownedU.transport second outV) (scan_code second (scan_code frame hc))
        (second.error.trans (frame.error.trans he)) (second.aligned (frame.aligned ha))
        pcV zero countV

/-- Once a nonzero Large left has been counted, both right-zero encodings take
the actual branch to normalize the original left, not the significant prefix. -/
theorem zero_right_counted_left (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (right : SszNative.NatOperand)
    (owned : Owned s (.large pointer words) right)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 64#64)
    (nonzero : (SszNative.NatOperand.large pointer words).wordCount ≠ 0)
    (zero : right.wordCount = 0)
    (count : r (.GPR 8#5) s = BitVec.ofNat 64 (sigWords words))
    (copy : r (.GPR 9#5) s = BitVec.ofNat 64 (sigWords words)) :
    ∃ fuel t, run fuel s = t ∧ Post s t (.large pointer words) right := by
  have hpc : r .PC s = base + 64#64 := hp
  cases right with
  | small word =>
    have wordZero := small_count_zero word zero
    subst word
    let ops : List Op := [.p64, .p68, .p96, .p572, .p576, .p580]
    let t := block base ops s
    have ptr : r (.GPR 1#5) s ≠ 0#64 := by
      rw [owned.leftPointer]
      change pointer ≠ 0#64
      have positive := owned.leftAt.1
      intro h
      simp [h] at positive
    have r3 : r (.GPR 3#5) s = 0#64 := owned.rightPointer
    have r4 : r (.GPR 4#5) s = 0#64 := owned.rightPayload
    have bound : sigWords words < 2^64 :=
      lt_of_le_of_lt (sigWords_le_length words) owned.operands.1.length_bound
    have countNonzero : r (.GPR 9#5) s ≠ 0#64 := by
      have h : sigWords words ≠ 0 := nonzero
      rw [copy]
      bv_omega
    have ran : run ops.length s = t := block_run base ops s hc he ha (by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, r3, r4, countNonzero, ptr, BitVec.add_assoc])
    have frame : NatCompare.Frame s t := scan_frame base ops s (by decide)
    have out : r (.GPR 0#5) t = r (.GPR 0#5) s := scan_zero base ops s (by decide)
    have pc : read_pc t = base + 584#64 := by
      simp [t, ops, block, Op.effect, put, next, state_simp_rules,
        hpc, r3, r4, countNonzero, ptr, BitVec.add_assoc]
    have index : r (.GPR 9#5) t = BitVec.ofNat 64 words.length - 1#64 := by
      simp [t, ops, block, Op.effect, put, next, state_simp_rules,
        owned.leftPayload, SszNative.NatOperand.payload]
    apply Post.prepend owned frame out ops.length ran
    exact zero_borrow_post false t base pointer words (.large pointer words) (.small 0#64)
      (owned.transport frame out) (scan_code frame hc) (frame.error.trans he)
      (frame.aligned ha) pc rfl index
      (SszNative.NatAdd.run_zero_right (.large pointer words) (.small 0#64)
        (arenaOf t).base (arenaOf t).capacity (arenaOf t).used nonzero zero)
  | large rightPointer rightWords =>
    let ops : List Op := [.p64]
    let t := block base ops s
    have ptr : r (.GPR 3#5) s ≠ 0#64 := by
      rw [owned.rightPointer]
      change rightPointer ≠ 0#64
      have positive := owned.rightAt.1
      intro h
      simp [h] at positive
    have ran : run ops.length s = t := block_run base ops s hc he ha (by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, ptr])
    have frame : NatCompare.Frame s t := scan_frame base ops s (by decide)
    have out : r (.GPR 0#5) t = r (.GPR 0#5) s := scan_zero base ops s (by decide)
    have pc : read_pc t = base + 300#64 := by
      simp [t, ops, block, Op.effect, put, next, state_simp_rules, ptr]
    have retained : r (.GPR 8#5) t = BitVec.ofNat 64 (sigWords words) := by
      simpa [t, ops, block, Op.effect, put, next, state_simp_rules] using count
    apply Post.prepend owned frame out ops.length ran
    exact zero_right_large_right t base rightPointer rightWords (.large pointer words)
      (owned.transport frame out) (scan_code frame hc) (frame.error.trans he)
      (frame.aligned ha) pc nonzero zero retained

/-- Full entry execution when only the right significant count is zero. -/
theorem zero_right_nonzero_left_correct (s : ArmState) (base : BitVec 64)
    (left right : SszNative.NatOperand) (owned : Owned s left right)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (nonzero : left.wordCount ≠ 0) (zero : right.wordCount = 0) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  cases left with
  | small word =>
    cases right with
    | small rightWord =>
      have rightZero := small_count_zero rightWord zero
      subst rightWord
      exact zero_right_small_small s base word owned hc he ha hp nonzero
    | large pointer words =>
      have ptr : r (.GPR 3#5) s ≠ 0#64 := by
        rw [owned.rightPointer]
        change pointer ≠ 0#64
        have positive := owned.rightAt.1
        intro h
        simp [h] at positive
      obtain ⟨fuel, t, ran, frame, out, count, pc⟩ :=
        small_large_start s base hc he ha hp owned.leftPointer ptr
      apply Post.prepend owned frame out fuel ran
      apply zero_right_large_right t base pointer words (.small word)
        (owned.transport frame out) (scan_code frame hc) (frame.error.trans he)
        (frame.aligned ha) pc nonzero zero
      simpa only [owned.leftPayload, SszNative.NatOperand.payload,
        SszNative.NatOperand.wordCount, SszNative.NatOperand.words] using count
  | large pointer words =>
    have ptr : r (.GPR 1#5) s ≠ 0#64 := by
      rw [owned.leftPointer]
      change pointer ≠ 0#64
      have positive := owned.leftAt.1
      intro h
      simp [h] at positive
    have notZero : sigWords words ≠ 0 := nonzero
    obtain ⟨fuel, t, ran, frame, out, count, copy, pc⟩ :=
      left_large_count s base words hc he ha hp owned.operands.1 ptr
    apply Post.prepend owned frame out fuel ran
    exact zero_right_counted_left t base pointer words right (owned.transport frame out)
      (scan_code frame hc) (frame.error.trans he) (frame.aligned ha)
      (by simpa only [notZero, ↓reduceIte] using pc) nonzero zero count copy

/-- Whole actual zero-operand slice: all Small/Large, empty and noncanonical
original representations, exact no-allocation resources, physical result and RET. -/
theorem zero_correct (s : ArmState) (base : BitVec 64)
    (left right : SszNative.NatOperand) (owned : Owned s left right)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (zero : left.wordCount = 0 ∨ right.wordCount = 0) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  by_cases leftZero : left.wordCount = 0
  · exact zero_left_correct s base left right owned hc he ha hp leftZero
  · exact zero_right_nonzero_left_correct s base left right owned hc he ha hp leftZero
      (zero.resolve_left leftZero)

end SszArm.NatAdd
