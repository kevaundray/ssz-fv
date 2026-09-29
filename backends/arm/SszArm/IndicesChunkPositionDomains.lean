import SszIndicesPaths

set_option autoImplicit false

namespace SszArm.Indices.ChunkPosition

open SszNative
open SszNative.Indices

/-- This discharges the specialized SHR domain without restricting the raw width
or the position representation. In particular empty and trailing-zero Large
operands are covered by the source packing test. -/
theorem packed_shift_le_five (width : NatOperand) (shift : Nat)
    (packed : packingShift width = some shift) : shift ≤ 5 := by
  unfold packingShift at packed
  split at packed
  · split at packed
    · have equation := Option.some.inj packed
      omega
    · contradiction
  · contradiction

theorem packed_shift_le_eight (width : NatOperand) (shift : Nat)
    (packed : packingShift width = some shift) : shift ≤ 8 := by
  have bound := packed_shift_le_five width shift packed
  omega

theorem packed_shift_word_domain (width : NatOperand) (shift : Nat)
    (packed : packingShift width = some shift) :
    (BitVec.ofNat 128 shift).toNat ≤ 8 := by
  have bound := packed_shift_le_eight width shift packed
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : shift < 2 ^ 128)]
  exact bound

/-- The other actual SHR call uses the literal bit-packing shift. -/
theorem bit_shift_word_domain : (8#128).toNat ≤ 8 := by decide

/-- An element error wins before the position tag, bounds, active bitmap, arena,
or any arithmetic is inspected. The unchanged outcome records no allocation. -/
theorem element_error_first (shape : Codec.Desc) (step : PathStep)
    (failure : Error) (base capacity used : Nat)
    (failed : elementType shape step = .error failure) :
    chunkPosition shape step base capacity used = unchanged used (.error failure) := by
  simp [chunkPosition, failed, bind, unchanged]

/-- Once the element lookup succeeds, each non-position constructor still fails
without executing an arithmetic call. -/
theorem nonposition_after_element (shape element : Codec.Desc) (step : PathStep)
    (base capacity used : Nat) (elementFound : elementType shape step = .ok element)
    (nonposition : ∀ ordinal, step ≠ .position ordinal) :
    chunkPosition shape step base capacity used = unchanged used (.error .notSteppable) := by
  cases step with
  | position ordinal => exact False.elim (nonposition ordinal rfl)
  | length => cases shape <;> simp [chunkPosition, elementFound, bind, unchanged]
  | activeFields => cases shape <;> simp [chunkPosition, elementFound, bind, unchanged]
  | selector => cases shape <;> simp [chunkPosition, elementFound, bind, unchanged]

/-- No canonicalization is applied to the ordinal in the container result. -/
theorem container_position (fields : List (String × Codec.Desc))
    (ordinal : NatOperand) (element : Codec.Desc) (base capacity used : Nat)
    (found : fieldType fields ordinal = .ok element) :
    chunkPosition (.container fields) (.position ordinal) base capacity used =
      unchanged used (.ok ⟨ordinal, .small 0, itemLength element⟩) := by
  simp [chunkPosition, elementType, found, bind, unchanged]

/-- The progressive-container bitmap is consulted only after field lookup. -/
theorem progressive_container_position (active : List Bool)
    (fields : List (String × Codec.Desc)) (ordinal : NatOperand)
    (element : Codec.Desc) (base capacity used : Nat)
    (found : fieldType fields ordinal = .ok element) :
    chunkPosition (.progressiveContainer active fields) (.position ordinal)
      base capacity used =
      bind (layoutPosition active ordinal base capacity used) (fun chunk used =>
        unchanged used (.ok ⟨chunk, .small 0, itemLength element⟩)) := by
  simp [chunkPosition, elementType, found]

/-- The source scan only returns an addressable byte inside the active slice.
This bound depends on the physical slice, not the logical ordinal value. -/
theorem active_scan_bounds (active : List Bool) (remaining position selected : Nat)
    (found : activeOrdinal active remaining position = some selected) :
    position ≤ selected ∧ selected < position + active.length := by
  induction active generalizing remaining position with
  | nil => simp [activeOrdinal] at found
  | cons present rest ih =>
      cases present with
      | false =>
          have bounds := ih remaining (position + 1) found
          simp only [List.length_cons]
          omega
      | true =>
          cases remaining with
          | zero =>
              simp only [activeOrdinal, Option.some.injEq] at found
              simp only [List.length_cons]
              omega
          | succ remaining =>
              have bounds := ih remaining (position + 1) found
              simp only [List.length_cons]
              omega

/-- At the active-position success branch the native from_u128 conversion is
necessarily Small; its input cannot overflow a word on a physical bool slice. -/
theorem active_scan_word_bound (active : List Bool) (remaining selected : Nat)
    (physical : active.length < 2 ^ 64)
    (found : activeOrdinal active remaining 0 = some selected) : selected < 2 ^ 64 := by
  have bounds := active_scan_bounds active remaining 0 selected found
  omega

/-- A failed conversion or an exhausted active scan preserves the raw ordinal
as the NoSuchField payload, including noncanonical representations. -/
theorem layout_unrepresentable (active : List Bool) (ordinal : NatOperand)
    (base capacity used : Nat) (conversion : ordinalToUsize ordinal = none) :
    layoutPosition active ordinal base capacity used =
      unchanged used (.error (.noSuchField ordinal)) := by
  simp [layoutPosition, activePosition, conversion, bind, unchanged]

theorem layout_exhausted (active : List Bool) (ordinal : NatOperand)
    (remaining base capacity used : Nat)
    (conversion : ordinalToUsize ordinal = some remaining)
    (exhausted : activeOrdinal active remaining 0 = none) :
    layoutPosition active ordinal base capacity used =
      unchanged used (.error (.noSuchField ordinal)) := by
  simp [layoutPosition, activePosition, conversion, exhausted, bind, unchanged]

/-- A multiplication failure does not attempt division or addition, but keeps
its complete arithmetic event and final cursor. -/
theorem unpacked_mul_error (position width : NatOperand) (base capacity used : Nat)
    (failure : NatArithmetic.Failure)
    (failed : (NatMul.run position width base capacity used).result = .error failure) :
    unpackedPosition position width base capacity used =
      ⟨.error (.arithmetic failure), (NatMul.run position width base capacity used).used,
        [.arithmetic used (NatMul.run position width base capacity used)]⟩ := by
  simp [unpackedPosition, bind, arithmetic, failed]

/-- Division failure retains the successful multiplication allocation and both
ordered events. There is no rollback to the original cursor. -/
theorem unpacked_div_error (position width product : NatOperand)
    (base capacity used : Nat) (failure : NatArithmetic.Failure)
    (multiplied : (NatMul.run position width base capacity used).result = .ok product)
    (failed : (NatDivision.run product 32 base capacity
      (NatMul.run position width base capacity used).used).result = .error failure) :
    unpackedPosition position width base capacity used =
      ⟨.error (.arithmetic failure),
        (NatDivision.run product 32 base capacity
          (NatMul.run position width base capacity used).used).used,
        [.arithmetic used (NatMul.run position width base capacity used),
          .divide (NatMul.run position width base capacity used).used
            (NatDivision.run product 32 base capacity
              (NatMul.run position width base capacity used).used)]⟩ := by
  simp [unpackedPosition, bind, arithmetic, divide, multiplied, failed]

end SszArm.Indices.ChunkPosition
