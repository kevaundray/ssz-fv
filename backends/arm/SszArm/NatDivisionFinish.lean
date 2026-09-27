import SszArm.NatDivisionReturn

namespace SszArm.NatDivision

open Delimited (Returned)
open UintCodec (widthLoad)
open UintCodec.Tail

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Result fields already serialized before the common suffix. The suffix is
responsible for the selected last word, the status, and all ABI restoration. -/
def ReturnReady (s : ArmState) :
    Except SszNative.NatArithmetic.Failure (SszNative.NatOperand × BitVec 64) → Prop
  | .ok (operand, remainder) =>
      r (.GPR 9#5) s = 16#64 ∧ r (.GPR 1#5) s = remainder ∧
      (r (.GPR 8#5) s).setWidth 32 = 0#32 ∧
      read_mem_bytes 8 (r (.GPR 19#5) s) s = operand.pointer ∧
      read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) s = operand.payload ∧
      operand.At (widthLoad s) ∧ OperandOwned (returnWrites s) operand
  | .error .scratchExhausted =>
      r (.GPR 9#5) s = 8#64 ∧ r (.GPR 1#5) s = 0#64 ∧
      (r (.GPR 8#5) s).setWidth 32 = 32768#32 ∧
      read_mem_bytes 8 (r (.GPR 19#5) s) s = 1#64 ∧
      (∀ n ∈ [16, 24, 32, 40, 48, 56],
        read_mem_bytes 8 (r (.GPR 19#5) s + BitVec.ofNat 64 n) s = 0#64)
  | .error .badRepresentation => False

/-- The common suffix does not rewrite any of the other initialized words. -/
theorem return_keeps_word (s : ArmState) (base : BitVec 64) (space : ReturnSpace s)
    (index : r (.GPR 9#5) s = 8#64 ∨ r (.GPR 9#5) s = 16#64)
    (offset : Nat) (low : offset % 8 = 0) (high : offset + 8 ≤ 64)
    (apart : BitVec.ofNat 64 offset ≠ r (.GPR 9#5) s) :
    read_mem_bytes 8 (r (.GPR 19#5) s + BitVec.ofNat 64 offset)
      (block base returnOps s) =
      read_mem_bytes 8 (r (.GPR 19#5) s + BitVec.ofNat 64 offset) s := by
  rcases space with ⟨stackLow, stackHigh, outputHigh, separate⟩
  rcases index with index | index
  all_goals
    have distinct : offset ≠ (r (.GPR 9#5) s).toNat := by
      intro same
      apply apart
      rw [same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    division_return_expand
    rw [index]
    rw [index] at distinct
    simp only [BitVec.toNat_ofNat] at distinct
    tail_reads

theorem return_result (s : ArmState) (base : BitVec 64) (space : ReturnSpace s)
    (result : Except SszNative.NatArithmetic.Failure (SszNative.NatOperand × BitVec 64))
    (ready : ReturnReady s result) :
    SszNative.NatArithmetic.DivisionResultAt (widthLoad (block base returnOps s))
      (r (.GPR 19#5) s).toNat result := by
  have toLoad (offset bytes : Nat) :
      widthLoad (block base returnOps s) ((r (.GPR 19#5) s).toNat + offset) bytes =
        some ((read_mem_bytes bytes (r (.GPR 19#5) s + BitVec.ofNat 64 offset)
          (block base returnOps s)).toNat) := by
    simp [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
  cases result with
  | ok pair =>
    rcases pair with ⟨operand, remainder⟩
    rcases ready with ⟨index, rem, status, pointer, payload, operandAt, owned⟩
    have selected := return_word s base space (Or.inr index)
    have flag := return_status s base space (Or.inr index)
    have p := return_keeps_word s base space (Or.inr index) 0 (by decide) (by decide)
      (by rw [index]; decide)
    have q := return_keeps_word s base space (Or.inr index) 8 (by decide) (by decide)
      (by rw [index]; decide)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at p
    rw [pointer] at p
    rw [payload] at q
    rw [index, rem] at selected
    rw [status] at flag
    refine ⟨⟨?_, ?_, operand_at_preserved (return_frame s base space (Or.inr index))
      operand operandAt owned⟩, ?_, ?_⟩
    · simpa only [Nat.add_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, p] using toLoad 0 8
    · simpa only [BitVec.ofNat_eq_ofNat, q] using toLoad 8 8
    · simpa only [BitVec.ofNat_eq_ofNat, selected] using toLoad 16 8
    · simpa only [BitVec.ofNat_eq_ofNat, flag, BitVec.toNat_ofNat] using toLoad 64 4
  | error failure =>
    cases failure with
    | badRepresentation => exact False.elim ready
    | scratchExhausted =>
      rcases ready with ⟨index, rem, status, pointer, zeros⟩
      have selected := return_word s base space (Or.inl index)
      have flag := return_status s base space (Or.inl index)
      have p := return_keeps_word s base space (Or.inl index) 0 (by decide) (by decide)
        (by rw [index]; decide)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at p
      rw [pointer] at p
      rw [index, rem] at selected
      rw [status] at flag
      have zero (n : Nat) (member : n ∈ [16, 24, 32, 40, 48, 56]) :
          widthLoad (block base returnOps s) ((r (.GPR 19#5) s).toNat + n) 8 = some 0 := by
        have bound : n + 8 ≤ 64 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
        have aligned : n % 8 = 0 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have apart : BitVec.ofNat 64 n ≠ r (.GPR 9#5) s := by
          rw [index]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have keep := return_keeps_word s base space (Or.inl index) n aligned bound apart
        rw [zeros n member] at keep
        simpa only [keep, BitVec.toNat_ofNat] using toLoad n 8
      refine ⟨?_, ?_, zero 16 (by simp), zero 24 (by simp), zero 32 (by simp),
        zero 40 (by simp), zero 48 (by simp), zero 56 (by simp), ?_⟩
      · simpa only [Nat.add_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, p,
          BitVec.toNat_ofNat] using toLoad 0 8
      · simpa only [BitVec.ofNat_eq_ofNat, selected, BitVec.toNat_ofNat] using toLoad 8 8
      · simpa only [BitVec.ofNat_eq_ofNat, flag, BitVec.toNat_ofNat] using toLoad 64 4

end SszArm.NatDivision
