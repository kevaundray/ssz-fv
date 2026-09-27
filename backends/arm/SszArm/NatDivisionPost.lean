import SszArm.NatDivisionFinish
import SszArm.NatDivisionEntry

namespace SszArm.NatDivision

open Delimited (Protected MemoryFrame)
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The common suffix uses only the original output and the bottom 16-byte
lowering slot, so its frame embeds in the caller's exact local footprint. -/
theorem return_local_frame {original s : ArmState} (base : BitVec 64)
    (operand : SszNative.NatOperand) (owned : Owned original operand)
    (saved : Saved original s) (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (index : r (.GPR 9#5) s = 8#64 ∨ r (.GPR 9#5) s = 16#64) :
    MemoryFrame (localWrites original) s (block base returnOps s) := by
  have frame := return_frame s base (owned.return_space saved.sp out) index
  have stack := owned.stackBound
  intro a outside
  apply frame a
  intro span member
  simp only [returnWrites, List.mem_cons, List.mem_singleton] at member
  rcases member with rfl | rfl
  · simpa only [out] using outside ((r (.GPR 0#5) original).toNat, 68) (by simp [localWrites])
  · have h := outside ((r (.GPR 31#5) original).toNat - 80, 80) (by simp [localWrites])
    simp only [Prod.fst, Prod.snd] at h ⊢
    rw [saved.sp]
    bv_omega

/-- Successful scratch words remain observable through serialization and RET.
Normalization never weakens the observation from full written limbs to a prefix. -/
theorem written_local_preserved {original s t : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand) (frame : MemoryFrame (localWrites original) s t)
    (written : WrittenAt (widthLoad s) (outcome original operand)) :
    WrittenAt (widthLoad t) (outcome original operand) := by
  intro reservation allocated i
  have resources := SszNative.NatDivision.allocation_resources operand (r (.GPR 3#5) original)
    (arenaOf original).base (arenaOf original).capacity (arenaOf original).used reservation allocated
  have separate := owned.fresh reservation allocated
  have local : Protected (localWrites original) reservation.pointer
      (8 * (outcome original operand).written.length) := by
    rcases separate with empty | separated
    · exact Or.inl empty
    · exact Or.inr (fun span member => separated span (List.mem_append_left _ member))
  have geometry := resources.2.2.1
  have pointer := resources.2.2.2.1
  have cursor := resources.2.2.2.2.1
  have length := resources.2.1
  have extent : reservation.pointer + 8 * (outcome original operand).written.length ≤ 2^64 := by
    have storage := owned.arenaStorage
    have cap := geometry.2.2.2.2.2
    rw [pointer, length]
    unfold SszNative.Arena.finish at cap
    omega
  have bound := i.isLt
  rw [frame.load _ _ (by omega) (local.subspan (8 * i.val) 8 (by omega))]
  exact written reservation allocated i

/-- Close the callee contract after the proved source/ISA body has prepared the
physical result. Only this internal phase theorem assumes body observations;
the public entry theorem must derive each of them from Owned. -/
theorem finish_post (original s : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (owned : Owned original operand)
    (saved : Saved original s) (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 976#64)
    (ready : ReturnReady s (outcome original operand).result)
    (written : WrittenAt (widthLoad s) (outcome original operand))
    (cursor : (read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) s).toNat =
      (outcome original operand).used)
    (before : MemoryFrame (writesFor original (outcome original operand)) original s) :
    Post original (run 13 s) operand := by
  have index : r (.GPR 9#5) s = 8#64 ∨ r (.GPR 9#5) s = 16#64 := by
    cases result : (outcome original operand).result with
    | ok pair => rw [result] at ready; exact Or.inr ready.1
    | error failure =>
      cases failure with
      | scratchExhausted => rw [result] at ready; exact Or.inl ready.1
      | badRepresentation => rw [result] at ready; exact False.elim ready
  rw [return_run s base hc he ha hp]
  have space := owned.return_space saved.sp out
  have after := return_local_frame base operand owned saved out index
  have arenaBound := owned.arenaBound
  have arenaAddress : (r (.GPR 4#5) original + 16#64).toNat =
      (r (.GPR 4#5) original).toNat + 16 := by bv_omega
  apply post_of_frame original _ operand owned
  · exact return_restores original s base saved space index he
  · simpa only [out] using return_result s base space _ ready
  · exact written_local_preserved owned after written
  · rw [after.read _ 8 (by rw [arenaAddress]; omega)]
    · exact cursor
    · rw [arenaAddress]
      exact owned.arenaLocal.subspan 16 8 (by decide)
  · exact before.trans (local_frame (outcome original operand) after)

end SszArm.NatDivision
