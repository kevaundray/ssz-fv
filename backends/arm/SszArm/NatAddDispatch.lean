import SszArm.NatAddFront
import SszArm.NatAddSelect

namespace SszArm.NatAdd

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem payload_nonzero {s : ArmState} {pointer payload : BitVec 64}
    {words : List (BitVec 64)} (input : NatCompare.Operand s pointer payload words)
    (nonzero : sigWords words ≠ 0) : payload ≠ 0#64 := by
  rcases input with ⟨_, rfl⟩ | ⟨_, count, source, memory⟩
  · intro zero
    simp [zero, sigWords, significantCount] at nonzero
  · intro zero
    have length : words.length = 0 := by simpa only [zero, BitVec.toNat_ofNat] using count.symm
    have empty := List.eq_nil_of_length_eq_zero length
    simp [empty, sigWords, significantCount] at nonzero

private theorem small_count {s : ArmState} {pointer payload : BitVec 64}
    {words : List (BitVec 64)} (input : NatCompare.Operand s pointer payload words)
    (small : pointer = 0#64) (nonzero : sigWords words ≠ 0) : sigWords words = 1 := by
  have word := input.small small
  have positive := payload_nonzero input nonzero
  simp [word, sigWords, significantCount, positive]

/-- Common continuation after any nonzero left count and a Large right operand. -/
theorem right_counted (s : ArmState) (base : BitVec 64) (leftCount : Nat)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 300#64)
    (leftPositive : 0 < leftCount) (leftBound : leftCount < 2^64)
    (rightNonzero : sigWords words ≠ 0)
    (leftReg : r (.GPR 8#5) s = BitVec.ofNat 64 leftCount)
    (input : NatCompare.Operand s (r (.GPR 3#5) s) (r (.GPR 4#5) s) words)
    (large : r (.GPR 3#5) s ≠ 0#64) :
    ∃ fuel t, run fuel s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 leftCount ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 (sigWords words) ∧
      r (.GPR 9#5) t = 1#64 ∧
      read_pc t = base + (if leftCount ≤ 1 ∧ sigWords words ≤ 1 then 384#64 else 128#64) := by
  obtain ⟨fuel, u, executed, frame, out, left, rawCount, right, pc⟩ :=
    right_large_count s base words hc he ha hp input large
  have rightBound : sigWords words < 2^64 :=
    Nat.lt_of_le_of_lt (sigWords_le_length words) input.length_bound
  obtain ⟨selected, selectionFrame, selectionOut, selectedLeft, selectedRight, tag, selectedPc⟩ :=
    width_select u base .largeRight leftCount (sigWords words) (scan_code frame hc)
      (frame.error.trans he) (frame.aligned ha)
      (by simpa only [rightNonzero, ↓reduceIte, WidthPath.start] using pc)
      leftPositive (Nat.pos_of_ne_zero rightNonzero) leftBound rightBound
      (left.trans leftReg) (right rightNonzero)
  refine ⟨fuel + WidthPath.largeRight.ops.length,
    block base WidthPath.largeRight.ops u, ?_, frame.trans selectionFrame,
    selectionOut.trans out, selectedLeft, selectedRight, ?_, selectedPc⟩
  · rw [run_plus, executed, selected]
  · exact tag

/-- The native entry chooses the immediate ADD or the significant-width branch.
All representation and width information remains about the original operands. -/
structure NonzeroEntry (s t : ArmState) (base : BitVec 64)
    (left right : SszNative.NatOperand) : Prop where
  frame : NatCompare.Frame s t
  out : r (.GPR 0#5) t = r (.GPR 0#5) s
  route :
    (read_pc t = base + 544#64 ∧ left.pointer = 0#64 ∧ right.pointer = 0#64) ∨
    (read_pc t = base + (if left.wordCount ≤ 1 ∧ right.wordCount ≤ 1 then 384#64 else 128#64) ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 left.wordCount ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 right.wordCount ∧
      r (.GPR 9#5) t = if right.pointer = 0#64 then 0#64 else 1#64)

theorem nonzero_entry (s : ArmState) (base : BitVec 64) (left right : SszNative.NatOperand)
    (owned : Owned s left right)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0) :
    ∃ fuel t, run fuel s = t ∧ NonzeroEntry s t base left right := by
  obtain ⟨leftInput, rightInput⟩ := owned.operands
  have leftBound : left.wordCount < 2^64 :=
    Nat.lt_of_le_of_lt (sigWords_le_length left.words) leftInput.length_bound
  have rightBound : right.wordCount < 2^64 :=
    Nat.lt_of_le_of_lt (sigWords_le_length right.words) rightInput.length_bound
  have leftPayload := payload_nonzero leftInput leftNonzero
  have rightPayload := payload_nonzero rightInput rightNonzero
  by_cases leftSmall : r (.GPR 1#5) s = 0#64
  · by_cases rightSmall : r (.GPR 3#5) s = 0#64
    · obtain ⟨executed, frame, out, pc⟩ := immediate_start s base hc he ha hp
        leftSmall rightSmall leftPayload rightPayload
      exact ⟨4, block base [.p0, .p72, .p76, .p540] s, executed,
        ⟨frame, out, Or.inl ⟨pc, owned.leftPointer.symm.trans leftSmall,
          owned.rightPointer.symm.trans rightSmall⟩⟩⟩
    · obtain ⟨fuel, u, executed, frame, out, leftCount, pc⟩ :=
        small_large_start s base hc he ha hp leftSmall rightSmall
      have count : r (.GPR 8#5) u = BitVec.ofNat 64 left.wordCount := by
        simpa only [SszNative.NatOperand.wordCount, leftInput.small leftSmall] using leftCount
      have input : NatCompare.Operand u (r (.GPR 3#5) u) (r (.GPR 4#5) u) right.words := by
        simpa only [frame.registers 3#5 (by decide), frame.registers 4#5 (by decide)] using
          frame.operand _ _ _ rightInput
      obtain ⟨steps, t, tailRun, tailFrame, tailOut, hleft, hright, tag, tailPc⟩ :=
        right_counted u base left.wordCount right.words (scan_code frame hc)
          (frame.error.trans he) (frame.aligned ha) pc (Nat.pos_of_ne_zero leftNonzero)
          leftBound rightNonzero count input
          (by simpa only [frame.registers 3#5 (by decide)] using rightSmall)
      refine ⟨fuel + steps, t, ?_, ⟨frame.trans tailFrame, tailOut.trans out,
        Or.inr ⟨tailPc, hleft, hright, ?_⟩⟩⟩
      · rw [run_plus, executed, tailRun]
      · have pointer : right.pointer ≠ 0#64 := by simpa only [owned.rightPointer] using rightSmall
        simpa only [pointer, ↓reduceIte] using tag
  · obtain ⟨fuel, u, executed, frame, out, leftCount, leftCopy, pc⟩ :=
      left_large_count s base left.words hc he ha hp leftInput leftSmall
    have copyNonzero : r (.GPR 9#5) u ≠ 0#64 := by
      rw [leftCopy]
      bv_omega
    have rightPayloadU : r (.GPR 3#5) u = 0#64 → r (.GPR 4#5) u ≠ 0#64 := by
      intro _
      simpa only [frame.registers 4#5 (by decide)] using rightPayload
    obtain ⟨routed, routeFrame, routeOut, routeLeft, routePc⟩ :=
      large_left_route u base (scan_code frame hc) (frame.error.trans he) (frame.aligned ha)
        (by simpa only [SszNative.NatOperand.wordCount] using
          (show read_pc u = base + 64#64 from by simpa only [leftNonzero, ↓reduceIte] using pc))
        copyNonzero rightPayloadU
    let v := block base (largeLeftRoute (r (.GPR 3#5) u)) u
    have combined : NatCompare.Frame s v := frame.trans routeFrame
    have combinedOut : r (.GPR 0#5) v = r (.GPR 0#5) s := routeOut.trans out
    have combinedLeft : r (.GPR 8#5) v = BitVec.ofNat 64 left.wordCount := routeLeft.trans leftCount
    have prefix : run (fuel + (largeLeftRoute (r (.GPR 3#5) u)).length) s = v := by
      rw [run_plus, executed, routed]
    by_cases rightSmall : r (.GPR 3#5) s = 0#64
    · have countOne : right.wordCount = 1 := small_count rightInput rightSmall rightNonzero
      have pcV : read_pc v = base + 108#64 := by
        simpa only [frame.registers 3#5 (by decide), rightSmall, ↓reduceIte] using routePc
      obtain ⟨selected, selectionFrame, selectionOut, selectedLeft, selectedRight, tag, selectedPc⟩ :=
        width_select v base .smallRight left.wordCount right.wordCount (scan_code combined hc)
          (combined.error.trans he) (combined.aligned ha) pcV (Nat.pos_of_ne_zero leftNonzero)
          (Nat.pos_of_ne_zero rightNonzero) leftBound rightBound combinedLeft countOne
      refine ⟨fuel + (largeLeftRoute (r (.GPR 3#5) u)).length + WidthPath.smallRight.ops.length,
        block base WidthPath.smallRight.ops v, ?_, ⟨combined.trans selectionFrame,
          selectionOut.trans combinedOut, Or.inr ⟨selectedPc, selectedLeft, selectedRight, ?_⟩⟩⟩
      · rw [run_plus, prefix, selected]
      · have pointer : right.pointer = 0#64 := owned.rightPointer.symm.trans rightSmall
        simpa only [pointer, ↓reduceIte] using tag
    · have pcV : read_pc v = base + 300#64 := by
        simpa only [frame.registers 3#5 (by decide), rightSmall, ↓reduceIte] using routePc
      have input : NatCompare.Operand v (r (.GPR 3#5) v) (r (.GPR 4#5) v) right.words := by
        simpa only [combined.registers 3#5 (by decide), combined.registers 4#5 (by decide)] using
          combined.operand _ _ _ rightInput
      obtain ⟨steps, t, tailRun, tailFrame, tailOut, hleft, hright, tag, tailPc⟩ :=
        right_counted v base left.wordCount right.words (scan_code combined hc)
          (combined.error.trans he) (combined.aligned ha) pcV (Nat.pos_of_ne_zero leftNonzero)
          leftBound rightNonzero combinedLeft input
          (by simpa only [combined.registers 3#5 (by decide)] using rightSmall)
      refine ⟨fuel + (largeLeftRoute (r (.GPR 3#5) u)).length + steps, t, ?_,
        ⟨combined.trans tailFrame, tailOut.trans combinedOut, Or.inr ⟨tailPc, hleft, hright, ?_⟩⟩⟩
      · rw [run_plus, prefix, tailRun]
      · have pointer : right.pointer ≠ 0#64 := by simpa only [owned.rightPointer] using rightSmall
        simpa only [pointer, ↓reduceIte] using tag

end SszArm.NatAdd
