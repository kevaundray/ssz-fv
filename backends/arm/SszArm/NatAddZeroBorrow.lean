import SszArm.NatAddZeroBorrowState

namespace SszArm.NatAdd

open UintCodec (widthLoad)
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Complete the native count-one collapse or multiword borrowed descriptor. -/
theorem borrow_normal_return (right : Bool) (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (if right then 472 else 636))
    (owned : ReturnOwned s)
    (input : (SszNative.NatOperand.large pointer words).At (widthLoad s))
    (borrowed : OperandOwned (localWrites s) (.large pointer words))
    (ptr : r (.GPR (borrowPointer right)) s = pointer)
    (positive : 0 < sigWords words)
    (count : r (.GPR 8#5) s = BitVec.ofNat 64 (sigWords words - 1)) :
    ZeroRun s (SszNative.NatOperand.fromWords pointer words) := by
  have length := sigWords_le_length words
  have extent := input.2.2.1
  have bound : sigWords words < 2^64 := by omega
  have small : sigWords words ≤ 1 ↔ sigWords words = 1 := by omega
  have low := original_low_word s pointer words input positive
  let one := decide (sigWords words = 1)
  let t := borrowNormalState right one base s
  have frame : ZeroFrame s t := borrow_normal_frame right one base s
  obtain ⟨follow, pc, pointerValue, payloadValue⟩ :=
    borrow_normal_observations right s base pointer (words[0]?.getD 0#64)
      (sigWords words) hp ptr positive bound count low
  change Follows base (borrowNormalOps right one) s at follow
  change read_pc t = base + BitVec.ofNat 64 (valueStart (borrowValuePath right)) at pc
  change valuePointer (borrowValuePath right) t =
    (if sigWords words = 1 then 0#64 else pointer) at pointerValue
  change valuePayload (borrowValuePath right) t =
    (if sigWords words = 1 then words[0]?.getD 0#64 else BitVec.ofNat 64 (sigWords words))
      at payloadValue
  have execution : run (borrowNormalOps right one).length s = t :=
    block_run base (borrowNormalOps right one) s hc he ha follow
  apply ZeroRun.prepend _ execution frame
  apply value_zero_run (borrowValuePath right) t base (frame.code hc)
    (frame.error.trans he) (frame.aligned ha) pc (frame.owned owned)
    (SszNative.NatOperand.fromWords pointer words)
  · simpa only [SszNative.NatOperand.fromWords_pointer, small,
      BitVec.ofNat_eq_ofNat] using pointerValue
  · simpa only [SszNative.NatOperand.fromWords_payload, small,
      BitVec.ofNat_eq_ofNat] using payloadValue
  · exact SszNative.NatOperand.fromWords_at _ pointer words
      (operand_at_preserved frame.memory _ input borrowed)
  · rw [frame.writes]
    exact fromWords_owned _ pointer words borrowed

/-- A full rescan of every supplied Large representation, followed by the real
borrowed/Small/zero stores and RET. Empty and all-zero slices are included. -/
theorem borrow_large_return (right : Bool) (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (borrowHead right))
    (owned : ReturnOwned s)
    (input : (SszNative.NatOperand.large pointer words).At (widthLoad s))
    (borrowed : OperandOwned (localWrites s) (.large pointer words))
    (ptr : r (.GPR (borrowPointer right)) s = pointer)
    (count : r (.GPR 9#5) s = BitVec.ofNat 64 words.length - 1#64)
    (source : NatCompare.Source s pointer words) (memory : NatCompare.Words s pointer words) :
    ZeroRun s (SszNative.NatOperand.fromWords pointer words) := by
  obtain ⟨fuel, t, execution, scanned, out, countAt, pc⟩ :=
    borrow_trim base pointer words right words.length s (Nat.le_refl _) hc he ha hp ptr count source memory
  have frame := ZeroFrame.of_scan scanned out owned.stack
  have inputAt := operand_at_preserved frame.memory (.large pointer words) input borrowed
  have ownedAt : OperandOwned (localWrites t) (.large pointer words) := by
    simpa only [frame.writes] using borrowed
  have full : significantCount words words.length = sigWords words := rfl
  rw [full] at countAt pc
  apply ZeroRun.prepend fuel execution frame
  by_cases zero : sigWords words = 0
  · have trimmed : SszNative.Limbs.trim words = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [SszNative.Limbs.trim_length, zero]
    have normalized : SszNative.NatOperand.fromWords pointer words = .small 0#64 := by
      simp only [SszNative.NatOperand.fromWords, trimmed]
    rw [normalized]
    apply value_zero_run (if right then .zeroRight else .zeroLeft) t base
      (frame.code hc) (frame.error.trans he) (frame.aligned ha)
      (by cases right <;> simpa [borrowExit, valueStart, zero] using pc)
      (frame.owned owned) (.small 0#64)
    · cases right <;> rfl
    · cases right <;> rfl
    · trivial
    · trivial
  · apply borrow_normal_return right t base pointer words (frame.code hc)
      (frame.error.trans he) (frame.aligned ha)
      (by simpa only [borrowExit, zero, ↓reduceIte] using pc)
      (frame.owned owned) inputAt ownedAt
    · exact (scanned.registers _ (by cases right <;> decide)).trans ptr
    · omega
    · exact countAt zero

end SszArm.NatAdd
