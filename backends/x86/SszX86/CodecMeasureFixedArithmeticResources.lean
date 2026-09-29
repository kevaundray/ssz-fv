import SszX86.EmitOwned
import SszX86.MeasureCore
import SszNatOperandNormalization
import SszNatDivision
import SszNatMul

namespace SszX86.CodecMeasureFixed
open SszNative

/-- Complete written storage, independent of the outcome's result type. -/
def ArithmeticWrites {α : Type} (call : NatArithmetic.Outcome α) (a : BitVec 64) : Prop :=
  ∃ reservation, call.allocation = some reservation ∧
    Emit.InSpan a (BitVec.ofNat 64 reservation.pointer) (8 * call.written.length)

theorem arithmeticWrites_singleton (call : NatArithmetic.Outcome NatOperand) (a : BitVec 64) :
    ArithmeticWrites call a ↔ Measure.AllocationWrites [call] a := by
  simp only [ArithmeticWrites, Measure.AllocationWrites, List.mem_singleton]
  constructor
  · rintro ⟨reservation, allocated, span⟩
    exact ⟨call, rfl, reservation, allocated, span⟩
  · rintro ⟨other, rfl, reservation, allocated, span⟩
    exact ⟨reservation, allocated, span⟩

theorem fromWords_borrowed (pointer : BitVec 64) (words : List (BitVec 64))
    (a : BitVec 64) (borrowed : Emit.NatBorrowed (NatOperand.fromWords pointer words) a) :
    Emit.InSpan a pointer (8 * words.length) := by
  have length : (Limbs.trim words).length ≤ words.length := by
    rw [Limbs.trim_length]
    exact Limbs.sigWords_le_length words
  cases trimmed : Limbs.trim words with
  | nil => simp only [NatOperand.fromWords, trimmed, Emit.NatBorrowed] at borrowed
  | cons first rest =>
    cases rest with
    | nil => simp only [NatOperand.fromWords, trimmed, Emit.NatBorrowed] at borrowed
    | cons second rest =>
      simp only [NatOperand.fromWords, trimmed, Emit.NatBorrowed, Emit.InSpan] at borrowed
      obtain ⟨i, bound, address⟩ := borrowed
      refine ⟨i, ?_, address⟩
      simp only [trimmed, List.length_cons] at length
      simp only [List.length_cons] at bound
      omega

theorem normalized_borrowed (operand : NatOperand) (a : BitVec 64)
    (borrowed : Emit.NatBorrowed operand.normalized a) : Emit.NatBorrowed operand a := by
  cases operand with
  | small limb =>
    by_cases zero : limb = 0#64
    · simp [NatOperand.normalized, NatOperand.fromWords, NatOperand.words,
        Limbs.trim, zero, Emit.NatBorrowed] at borrowed
    · simp [NatOperand.normalized, NatOperand.fromWords, NatOperand.words,
        Limbs.trim, zero, Emit.NatBorrowed] at borrowed
  | large pointer words => exact fromWords_borrowed pointer words a borrowed

/-- Success provenance is a footprint statement, not a future machine premise. -/
def ArithmeticProvenance (input : BitVec 64 → Prop)
    (call : NatArithmetic.Outcome NatOperand) : Prop :=
  ∀ result, call.result = .ok result → ∀ a, Emit.NatBorrowed result a →
    input a ∨ ArithmeticWrites call a

theorem unchanged_normalized_provenance (operand : NatOperand) (used : Nat) :
    ArithmeticProvenance (Emit.NatBorrowed operand)
      (NatArithmetic.unchanged used (.ok operand.normalized)) := by
  intro result success a borrowed
  cases success
  exact Or.inl (normalized_borrowed operand a borrowed)

theorem unchanged_small_provenance (input : BitVec 64 → Prop) (used : Nat) (limb : BitVec 64) :
    ArithmeticProvenance input (NatArithmetic.unchanged used (.ok (.small limb))) := by
  intro result success a borrowed
  cases success
  exact False.elim borrowed

theorem unchanged_error_provenance (input : BitVec 64 → Prop) (used : Nat)
    (error : NatArithmetic.Failure) :
    ArithmeticProvenance input (NatArithmetic.unchanged used (.error error)) := by
  intro result success
  cases success

theorem committed_provenance (input : BitVec 64 → Prop) (reservation : Arena.Reservation)
    (words : List (BitVec 64)) :
    ArithmeticProvenance input (NatArithmetic.committed reservation words) := by
  intro result success a borrowed
  cases success
  exact Or.inr ⟨reservation, rfl, fromWords_borrowed _ words a borrowed⟩

theorem fromWide_provenance (input : BitVec 64 → Prop) (base capacity used : Nat)
    (wide : BitVec 128) :
    ArithmeticProvenance input (NatArithmetic.fromWide base capacity used wide) := by
  unfold NatArithmetic.fromWide
  split
  · exact unchanged_small_provenance _ _ _
  · split
    · exact unchanged_error_provenance _ _ _
    · exact committed_provenance _ _ _

theorem arithmeticProvenance_mono {input larger : BitVec 64 → Prop}
    {call : NatArithmetic.Outcome NatOperand} (h : ArithmeticProvenance input call)
    (hinclude : ∀ a, input a → larger a) : ArithmeticProvenance larger call := by
  intro result success a borrowed
  exact (h result success a borrowed).imp (hinclude a) id

theorem add_result_provenance (left right : NatOperand) (base capacity used : Nat) :
    ArithmeticProvenance (fun a => Emit.NatBorrowed left a ∨ Emit.NatBorrowed right a)
      (SszNative.NatAdd.run left right base capacity used) := by
  dsimp only [SszNative.NatAdd.run]
  split
  · exact arithmeticProvenance_mono (unchanged_normalized_provenance right used)
      (fun _ => Or.inr)
  · split
    · exact arithmeticProvenance_mono (unchanged_normalized_provenance left used)
        (fun _ => Or.inl)
    · split
      · exact fromWide_provenance _ _ _ _ _
      · split
        · split
          · exact unchanged_error_provenance _ _ _
          · exact committed_provenance _ _ _
        · exact unchanged_error_provenance _ _ _

end SszX86.CodecMeasureFixed
