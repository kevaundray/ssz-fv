import SszIndicesDescriptor
import SszCodecTypesProofs
import SszNatNarrow
import SszNatAdd

set_option autoImplicit false

namespace SszNative.Indices

@[simp] theorem small_value (word : BitVec 64) :
    (NatOperand.small word).value = word.toNat := by
  simp [NatOperand.value, NatOperand.words, Limbs.value]

@[simp] theorem nativeCmp_eq_iff (left right : NatOperand) :
    Limbs.nativeCmp left.words right.words = .eq ↔ left.value = right.value := by
  simp only [Limbs.nativeCmp_correct, Nat.compare_eq_eq, NatOperand.value]

@[simp] theorem nativeCmp_not_lt_iff (left right : NatOperand) :
    Limbs.nativeCmp left.words right.words ≠ .lt ↔ right.value ≤ left.value := by
  simp only [Limbs.nativeCmp_correct, ne_eq, Nat.compare_eq_lt, Nat.not_lt, NatOperand.value]

/-- Observation bridge for the source's significant-word conversion. -/
theorem ordinalToUsize_refines (ordinal : NatOperand) :
    ordinalToUsize ordinal = if ordinal.value < 2^64 then some ordinal.value else none := by
  have fitsIff := ordinal.wordCount_le_iff_value_lt 1
  simp only [Nat.mul_one] at fitsIff
  by_cases fits : ordinal.wordCount ≤ 1
  · have wordValue : (word ordinal 0).toNat = ordinal.value := by
      rw [word_eq]
      exact NatAdd.lowWord_value ordinal fits
    simp only [ordinalToUsize, fits, fitsIff.mp fits, ↓reduceIte, wordValue]
  · have large : ¬ ordinal.value < 2^64 := fun small => fits (fitsIff.mpr small)
    simp only [ordinalToUsize, fits, large, ↓reduceIte]

/-- Raw invalid widths are included; this theorem has no schema-validity premise. -/
theorem itemLength_refines (shape : Codec.Desc) :
    (itemLength shape).value = shape.erase.itemLength := by
  cases shape with
  | primitive shape => cases shape <;>
      simp [itemLength, Codec.Desc.erase, Serialize.Desc.erase, Ssz.Desc.itemLength,
        Ssz.bytesPerChunk]
  | _ => simp [itemLength, Codec.Desc.erase, Ssz.Desc.itemLength, Ssz.bytesPerChunk]

theorem positionCount_refines (shape : Codec.Desc) :
    eraseResult ((positionCount shape).map (Option.map NatOperand.value)) =
      .ok shape.erase.positionCount := by
  cases shape with
  | primitive shape => cases shape <;> rfl
  | _ => rfl

theorem mixesIn_refines (shape : Codec.Desc) (step : PathStep) :
    mixesIn shape step = shape.erase.mixesIn step.erase := by
  cases shape with
  | primitive shape => cases shape <;> cases step <;> rfl
  | _ => cases step <;> rfl

/-- The native forward scan and the pinned ordinal recursion agree even if the
active mask and the field slice have unrelated lengths. -/
theorem activeOrdinal_refines (active : List Bool) (ordinal position : Nat) :
    activeOrdinal active ordinal position =
      (Ssz.activePosition active ordinal).map (position + ·) := by
  induction active generalizing ordinal position with
  | nil => rfl
  | cons present rest ih =>
      cases present with
      | false =>
          simp only [activeOrdinal, Ssz.activePosition, ih, Option.map_map]
          congr 1
          funext value
          dsimp only [Function.comp_def]
          omega
      | true =>
          cases ordinal with
          | zero => simp [activeOrdinal, Ssz.activePosition]
          | succ ordinal =>
              simp only [activeOrdinal, Ssz.activePosition, ih, Option.map_map]
              congr 1
              funext value
              dsimp only [Function.comp_def]
              omega

theorem activeOrdinal_bound (active : List Bool) (ordinal position result : Nat)
    (found : activeOrdinal active ordinal position = some result) :
    position ≤ result ∧ result < position + active.length := by
  induction active generalizing ordinal position with
  | nil => cases found
  | cons present rest ih =>
      cases present with
      | false =>
          have bound := ih ordinal (position + 1) found
          simp only [List.length_cons]
          omega
      | true =>
          cases ordinal with
          | zero =>
              simp only [activeOrdinal, Option.some.injEq] at found
              subst result
              simp
          | succ ordinal =>
              have bound := ih ordinal (position + 1) found
              simp only [List.length_cons]
              omega

theorem activeOrdinal_ordinal_bound (active : List Bool) (ordinal position result : Nat)
    (found : activeOrdinal active ordinal position = some result) : ordinal < active.length := by
  induction active generalizing ordinal position with
  | nil => cases found
  | cons present rest ih =>
      cases present with
      | false =>
          have bound := ih ordinal (position + 1) found
          simp only [List.length_cons]
          omega
      | true =>
          cases ordinal with
          | zero => simp
          | succ ordinal =>
              have bound := ih ordinal (position + 1) found
              simp only [List.length_cons]
              omega

theorem activeOrdinal_large_missing (active : List Bool) (ordinal : NatOperand)
    (physical : active.length < 2^64) (large : ¬ ordinal.value < 2^64) :
    Ssz.activePosition active ordinal.value = none := by
  cases result : Ssz.activePosition active ordinal.value with
  | none => rfl
  | some position =>
      have found : activeOrdinal active ordinal.value 0 = some position := by
        simp [activeOrdinal_refines, result]
      have bound := activeOrdinal_ordinal_bound active ordinal.value 0 position found
      omega

/-- Conversion failure is semantic absence only because this is a physical slice
bound, never a restriction on the logical ordinal. -/
theorem fieldType_refines (fields : List (String × Codec.Desc)) (ordinal : NatOperand)
    (physical : fields.length < 2^64) :
    eraseResult ((fieldType fields ordinal).map Codec.Desc.erase) =
      .ok (match (Codec.Desc.eraseFields fields)[ordinal.value]? with
        | none => .error (.noSuchField ordinal.value)
        | some child => .ok child) := by
  unfold fieldType
  rw [ordinalToUsize_refines]
  by_cases fits : ordinal.value < 2^64
  · simp only [fits, ↓reduceIte]
    rw [Codec.Desc.eraseFields_eq_map, List.getElem?_map]
    cases found : fields[ordinal.value]? <;> rfl
  · have outside : fields.length ≤ ordinal.value := by omega
    have missing : fields[ordinal.value]? = none := List.getElem?_eq_none outside
    have erasedMissing : (Codec.Desc.eraseFields fields)[ordinal.value]? = none := by
      rw [Codec.Desc.eraseFields_eq_map, List.getElem?_map, missing]
      rfl
    simp only [fits, ↓reduceIte, erasedMissing]
    rfl

theorem elementType_refines (shape : Codec.Desc) (step : PathStep)
    (physical : shape.Physical) :
    eraseResult ((elementType shape step).map Codec.Desc.erase) =
      .ok (shape.erase.elementType step.erase) := by
  cases shape with
  | primitive shape => cases shape <;> cases step <;> rfl
  | vector element count => cases step <;> rfl
  | list element count => cases step <;> rfl
  | progressiveList element count => cases step <;> rfl
  | compatibleUnion variants => cases step <;> rfl
  | container fields =>
      cases step with
      | position ordinal =>
          have refined := fieldType_refines fields ordinal physical.1
          cases found : (Codec.Desc.eraseFields fields)[ordinal.value]? <;>
            simpa only [elementType, Codec.Desc.erase, PathStep.erase, Ssz.Desc.elementType,
              found] using refined
      | _ => rfl
  | progressiveContainer active fields =>
      cases step with
      | position ordinal =>
          have refined := fieldType_refines fields ordinal physical.2.1
          cases found : (Codec.Desc.eraseFields fields)[ordinal.value]? <;>
            simpa only [elementType, Codec.Desc.erase, PathStep.erase, Ssz.Desc.elementType,
              found] using refined
      | _ => rfl

/-- Looking at a matching head never inspects a duplicate later selector. -/
theorem unionOption_first (selector ordinal : NatOperand) (child : Codec.Desc)
    (rest : List (NatOperand × Codec.Desc)) (same : selector.value = ordinal.value) :
    unionOption ((selector, child) :: rest) ordinal = some child := by
  simp only [unionOption, nativeCmp_eq_iff, same, ↓reduceIte]

/-- Physical positions always use the small from_u128 branch on both native ABIs. -/
theorem fromWide_position (position base capacity used : Nat) (physical : position < 2^64) :
    NatArithmetic.fromWide base capacity used (BitVec.ofNat 128 position) =
      NatArithmetic.unchanged used (.ok (.small (BitVec.ofNat 64 position))) := by
  have wideBound : position < 2^128 := by omega
  have narrow : (BitVec.ofNat 128 position).setWidth 64 = BitVec.ofNat 64 position := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wideBound]
  simp only [NatArithmetic.fromWide, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt wideBound, physical, ↓reduceIte, narrow]

theorem activePosition_found (active : List Bool) (ordinal : NatOperand)
    (position base capacity used : Nat) (fits : ordinal.value < 2^64)
    (found : activeOrdinal active ordinal.value 0 = some position)
    (physical : position < 2^64) :
    activePosition active ordinal base capacity used =
      ⟨.ok (some (.small (BitVec.ofNat 64 position))), used,
        [.arithmetic used (NatArithmetic.unchanged used
          (.ok (.small (BitVec.ofNat 64 position))))]⟩ := by
  simp only [activePosition, ordinalToUsize_refines, fits, ↓reduceIte, found,
    fromWide_position position base capacity used physical, arithmetic,
    NatArithmetic.unchanged, Except.mapError, bind, unchanged, List.append_nil]

theorem activePosition_refines (active : List Bool) (ordinal : NatOperand)
    (base capacity used : Nat) (physical : active.length < 2^64) :
    eraseResult ((activePosition active ordinal base capacity used).result.map
      (Option.map NatOperand.value)) =
      .ok (.ok (Ssz.activePosition active ordinal.value)) := by
  by_cases fits : ordinal.value < 2^64
  · cases found : activeOrdinal active ordinal.value 0 with
    | none =>
        have erasedFound : Ssz.activePosition active ordinal.value = none := by
          simpa [found] using (activeOrdinal_refines active ordinal.value 0).symm
        simp only [activePosition, ordinalToUsize_refines, fits, ↓reduceIte, found,
          unchanged, Except.map, Option.map, eraseResult, erasedFound]
    | some position =>
        have erasedFound : Ssz.activePosition active ordinal.value = some position := by
          simpa [found] using (activeOrdinal_refines active ordinal.value 0).symm
        have bound := activeOrdinal_bound active ordinal.value 0 position found
        have small : position < 2^64 := by omega
        rw [activePosition_found active ordinal position base capacity used fits found small]
        simp only [Except.map, Option.map, eraseResult, erasedFound, small_value,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  · have missing := activeOrdinal_large_missing active ordinal physical fits
    simp only [activePosition, ordinalToUsize_refines, fits, ↓reduceIte, unchanged,
      Except.map, Option.map, eraseResult, missing]

theorem layoutPosition_refines (active : List Bool) (ordinal : NatOperand)
    (base capacity used : Nat) (physical : active.length < 2^64) :
    eraseResult ((layoutPosition active ordinal base capacity used).result.map
      NatOperand.value) = .ok (Ssz.layoutPosition active ordinal.value) := by
  have refined := activePosition_refines active ordinal base capacity used physical
  cases outcome : (activePosition active ordinal base capacity used).result with
  | error reason =>
      cases reason <;> simp only [outcome, Except.map, eraseResult] at refined <;>
        cases refined
  | ok position =>
      cases position with
      | none =>
          simp only [outcome, Except.map, Option.map, eraseResult,
            Except.ok.injEq] at refined
          simp only [layoutPosition, bind, outcome, unchanged, Except.map, eraseResult,
            Ssz.layoutPosition, ← refined]
      | some position =>
          simp only [outcome, Except.map, Option.map, eraseResult,
            Except.ok.injEq] at refined
          simp only [layoutPosition, bind, outcome, unchanged, Except.map, eraseResult,
            Ssz.layoutPosition, ← refined]

theorem fieldType_member (fields : List (String × Codec.Desc)) (ordinal : NatOperand)
    (child : Codec.Desc) (success : fieldType fields ordinal = .ok child) :
    child ∈ fields.map Prod.snd := by
  unfold fieldType at success
  cases converted : ordinalToUsize ordinal with
  | none => simp [converted] at success
  | some position =>
      cases found : fields[position]? with
      | none => simp [converted, found] at success
      | some field =>
          simp only [converted, found, Except.ok.injEq] at success
          exact List.mem_map.mpr ⟨field, List.mem_of_getElem? found, success⟩

theorem elementType_physical (shape : Codec.Desc) (step : PathStep) (child : Codec.Desc)
    (physical : shape.Physical) (success : elementType shape step = .ok child) :
    child.Physical := by
  cases shape with
  | primitive shape =>
      cases shape <;> cases step <;>
        simp only [elementType] at success <;> cases success <;> trivial
  | vector element count =>
      cases step <;> simp only [elementType, Except.ok.injEq] at success <;>
        subst child <;> exact physical.1
  | list element count =>
      cases step <;> simp only [elementType, Except.ok.injEq] at success <;>
        subst child <;> exact physical.1
  | progressiveList element count =>
      cases step <;> simp only [elementType, Except.ok.injEq] at success <;>
        subst child <;> exact physical.1
  | compatibleUnion variants => cases step <;> cases success
  | container fields =>
      cases step with
      | position ordinal =>
          exact Codec.Desc.physical_child _ child physical
            (fieldType_member fields ordinal child success)
      | _ => cases success
  | progressiveContainer active fields =>
      cases step with
      | position ordinal =>
          exact Codec.Desc.physical_child _ child physical
            (fieldType_member fields ordinal child success)
      | _ => cases success

theorem unionOption_member (variants : List (NatOperand × Codec.Desc))
    (ordinal : NatOperand) (child : Codec.Desc)
    (success : unionOption variants ordinal = some child) :
    child ∈ variants.map Prod.snd := by
  induction variants with
  | nil => cases success
  | cons variant rest ih =>
      unfold unionOption at success
      split at success
      · simp only [Option.some.injEq] at success
        simp [success]
      · exact List.mem_cons_of_mem _ (ih success)

theorem unionOption_physical (variants : List (NatOperand × Codec.Desc))
    (ordinal : NatOperand) (child : Codec.Desc)
    (physical : (Codec.Desc.compatibleUnion variants).Physical)
    (success : unionOption variants ordinal = some child) : child.Physical :=
  Codec.Desc.physical_child _ child physical (unionOption_member variants ordinal child success)

end SszNative.Indices
