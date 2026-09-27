import SszArm.NatAddZeroBorrow
import SszArm.NatAddPostTransport

namespace SszArm.NatAdd

open UintCodec (widthLoad)
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem small_normalized (word : BitVec 64) :
    (SszNative.NatOperand.small word).normalized = .small word := by
  by_cases zero : word = 0#64 <;>
    simp [SszNative.NatOperand.normalized, SszNative.NatOperand.words,
      SszNative.NatOperand.pointer, SszNative.NatOperand.fromWords,
      SszNative.Limbs.trim, zero]

theorem small_count_zero (word : BitVec 64)
    (zero : (SszNative.NatOperand.small word).wordCount = 0) : word = 0#64 := by
  by_cases h : word = 0#64
  · exact h
  · simp [SszNative.NatOperand.wordCount, SszNative.NatOperand.words,
      sigWords, significantCount, h] at zero

theorem zero_small_post (path : StatusPath) (s : ArmState) (base word : BitVec 64)
    (left right : SszNative.NatOperand) (owned : Owned s left right)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (valueStart path))
    (pointer : valuePointer path s = 0#64) (payload : valuePayload path s = word)
    (model : outcome s left right = SszNative.NatArithmetic.unchanged (arenaOf s).used (.ok (.small word))) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  exact (value_zero_run path s base hc he ha hp owned.return_owned (.small word)
    pointer payload trivial trivial).post owned model

/-- Adapt the original input selected by the zero branch to the complete borrowed
return certificate. No normalized/canonical input assumption is introduced. -/
theorem zero_borrow_post (side : Bool) (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (left right : SszNative.NatOperand)
    (owned : Owned s left right)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (borrowHead side))
    (selected : (if side then right else left) = .large pointer words)
    (count : r (.GPR 9#5) s = BitVec.ofNat 64 words.length - 1#64)
    (model : outcome s left right = SszNative.NatArithmetic.unchanged (arenaOf s).used
      (.ok (SszNative.NatOperand.fromWords pointer words))) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  have input : (if side then right else left).At (widthLoad s) := by
    cases side
    · exact owned.leftAt
    · exact owned.rightAt
  rw [selected] at input
  have borrowed : OperandOwned (writesFor s (outcome s left right)) (if side then right else left) := by
    cases side
    · exact owned.leftOwned
    · exact owned.rightOwned
  rw [selected, model] at borrowed
  change OperandOwned (localWrites s) (.large pointer words) at borrowed
  have ptr : r (.GPR (borrowPointer side)) s = (if side then right else left).pointer := by
    cases side
    · exact owned.leftPointer
    · exact owned.rightPointer
  rw [selected] at ptr
  change r (.GPR (borrowPointer side)) s = pointer at ptr
  have original : NatCompare.Operand s (r (.GPR (borrowPointer side)) s)
      (r (.GPR (if side then 4#5 else 2#5)) s) (if side then right else left).words := by
    cases side
    · exact owned.operands.1
    · exact owned.operands.2
  rw [selected] at original
  have nonzero : r (.GPR (borrowPointer side)) s ≠ 0#64 := by
    rw [ptr]
    have positive := input.1
    intro zero
    simp [zero] at positive
  obtain ⟨payload, source, memory⟩ := original.large nonzero
  rw [ptr] at source memory
  exact (borrow_large_return side s base pointer words hc he ha hp owned.return_owned
    input borrowed ptr count source memory).post owned model

end SszArm.NatAdd
