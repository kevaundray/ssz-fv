import SszArm.NatMulWordLargeFirst
import SszArm.NatMulWordSmallFrame
import SszArm.NatMulWordNormalize

namespace SszArm.NatMulWord.Large

open UintCodec (widthLoad)
open Delimited (MemoryFrame Protected Returned)

/-- The large reservation prefix has only its real lowering-slot write. -/
theorem reserve_small {s t : ArmState} (priorFrame : Reserve.Prefix s t)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) : SmallFrame s t := by
  refine ⟨⟨priorFrame.frame.program, priorFrame.frame.error, ?_, priorFrame.frame.vectors⟩, ?_⟩
  · intro reg keep
    apply priorFrame.frame.registers
    simp_all only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  · intro a outside
    have outer := outside ((r (.GPR 31#5) s).toNat - 48, 48) (by simp)
    apply priorFrame.memoryFrame (by omega) a
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    simp only [Prod.fst, Prod.snd] at outer ⊢
    omega

theorem setup_abi (s : ArmState) (base : BitVec 64) :
    SmallABI s (block base Reserve.firstOps s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩
  · intro reg keep
    apply Reserve.first_registers s base reg
    simp_all only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  · intro reg
    exact Reserve.block_preserves (r (.SFP reg)) base Reserve.firstOps
      (fun op _ t => op.sfp base t reg) s

theorem FirstPost.abi {s t : ArmState} {base : BitVec 64}
    (post : FirstPost s t base) : SmallABI s t := by
  refine ⟨post.program, post.error, ?_, post.vectors⟩
  intro reg keep
  apply post.registers
  simp_all

/-- The original error body is composed with the already executed read-only
reservation/scan prefix. The checked model equation is obtained at the guard exit. -/
theorem error_finish (s u : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (factor : BitVec 64) (path : ErrorPath)
    (owned : Owned s operand factor) (priorFrame : SmallFrame s u)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc u = base + BitVec.ofNat 64 path.start)
    (model : outcome s operand factor =
      SszNative.NatArithmetic.unchanged (arenaOf s).used (.error .scratchExhausted)) :
    run 50 u = errorResult path base u ∧ Post s (errorResult path base u) operand factor := by
  have returns := priorFrame.return_owned owned.return_owned
  obtain ⟨ran, returned, image, changed⟩ := error_run_contract path u base
    (priorFrame.code code) (priorFrame.error.trans error) (priorFrame.aligned aligned) pc returns
  refine ⟨ran, small_unchanged_post s _ operand factor owned (.error .scratchExhausted)
    model (priorFrame.returned returned) ?_ ?_⟩
  · simpa only [priorFrame.out] using image
  · apply (priorFrame.full (outcome s operand factor)).trans
    intro a outside
    apply changed a
    have stack := outside ((r (.GPR 31#5) s).toNat - 48, 48)
      (by simp [writesFor, localWrites, model, SszNative.NatArithmetic.unchanged])
    have output := outside ((r (.GPR 0#5) s).toNat, 68)
      (by simp [writesFor, localWrites, model, SszNative.NatArithmetic.unchanged])
    intro span member
    simp only [errorWrites, NatAdd.localWrites, priorFrame.sp, priorFrame.out,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp only [Prod.fst, Prod.snd] at * <;>
      have bound := owned.stackBound <;> omega

/-- The complete fresh allocation lies in the original physical arena extent.
No isize constraint on arena capacity is introduced. -/
structure AllocationSpace (s : ArmState) (reservation : SszNative.Arena.Reservation)
    (count : Nat) : Prop where
  pointerBound : reservation.pointer < 2^64
  positive : 0 < reservation.pointer
  aligned : reservation.pointer % 8 = 0
  physical : reservation.pointer + 8 * count ≤ 2^64
  stack : NatMul.LoopSpace (r (.GPR 31#5) s) (BitVec.ofNat 64 reservation.pointer) count
  separate : Protected (localWrites s
      (SszNative.NatArithmetic.committed reservation (List.replicate count 0#64)) ++
      [((r (.GPR 4#5) s).toNat, 24)]) reservation.pointer (8 * count)

theorem allocation_space (s : ArmState) (operand : SszNative.NatOperand) (factor : BitVec 64)
    (owned : Owned s operand factor) (reservation : SszNative.Arena.Reservation)
    (positive : 0 < operand.wordCount + 1)
    (reserved : SszNative.Arena.reserve (arenaOf s).base (arenaOf s).capacity (arenaOf s).used
      (operand.wordCount + 1) = some reservation)
    (model : outcome s operand factor = SszNative.NatArithmetic.committed reservation
      (SszNative.NatMul.wordWritten operand factor)) :
    AllocationSpace s reservation (operand.wordCount + 1) := by
  obtain ⟨checks, value⟩ := (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _ positive reservation).1 reserved
  have cursor := SszNative.Arena.used_le_start (arenaOf s).base (arenaOf s).used
  have finish := checks.2.2.2.2.2
  have storage := owned.arenaStorage
  have reservationEnd : reservation.pointer + 8 * (operand.wordCount + 1) ≤ 2^64 := by
    rw [value]
    simp only [SszNative.Arena.finish] at finish ⊢
    omega
  have pointerBound : reservation.pointer < 2^64 := by omega
  have nonnull := owned.arenaNonnull (by simp only [SszNative.Arena.finish] at finish; omega)
  have pointerPositive : 0 < reservation.pointer := by rw [value]; simp only; omega
  have pointerAligned : reservation.pointer % 8 = 0 := by
    rw [value]
    change ((arenaOf s).base + SszNative.Arena.start (arenaOf s).base (arenaOf s).used) % 8 = 0
    rw [SszNative.Arena.start_pointer]
    exact SszNative.Arena.aligned_mod _
  have fresh := owned.fresh reservation (by rw [model]; rfl)
  rw [model] at fresh
  simp only [SszNative.NatArithmetic.committed, SszNative.NatMul.wordWritten_length] at fresh
  have sep : Protected (localWrites s (SszNative.NatArithmetic.committed reservation
      (List.replicate (operand.wordCount + 1) 0#64)) ++ [((r (.GPR 4#5) s).toNat, 24)])
      reservation.pointer (8 * (operand.wordCount + 1)) := by
    simpa only [localWrites, SszNative.NatArithmetic.committed] using fresh
  have apart : reservation.pointer + 8 * (operand.wordCount + 1) ≤
      (r (.GPR 31#5) s).toNat - 48 ∨ (r (.GPR 31#5) s).toNat ≤ reservation.pointer := by
    rcases sep with empty | separated
    · omega
    · have h := separated ((r (.GPR 31#5) s).toNat - 48, 48)
        (by simp [localWrites, SszNative.NatArithmetic.committed])
      have bound := owned.stackBound
      simp only [Prod.fst, Prod.snd] at h
      omega
  refine ⟨pointerBound, pointerPositive, pointerAligned, reservationEnd,
    ⟨owned.stackBound, ?_, ?_⟩, sep⟩
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound] using reservationEnd
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound] using apart

end SszArm.NatMulWord.Large
