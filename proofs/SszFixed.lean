import Std
import Ssz.Type.Desc

set_option autoImplicit false

namespace SszNative.Fixed

/- Algorithm model of native/src/schema.rs:is_fixed. It examines only type
constructors, never computes widths or capacities. These equations concern
structural classification, not native pointer traversal or ISA execution. -/
mutual
  def classify : Ssz.Desc → Bool
    | .bool | .uint _ | .byteVector _ | .bitVector _ => true
    | .vector element _ => classify element
    | .container _ fields | .progressiveContainer _ _ fields => classifyFields fields
    | _ => false

  def classifyFields : List Ssz.Desc → Bool
    | [] => true
    | field :: rest => classify field && classifyFields rest
end

mutual
  theorem classify_eq (desc : Ssz.Desc) :
      classify desc = desc.fixedSize.isSome := by
    cases desc with
    | vector element length =>
      simp only [classify, Ssz.Desc.fixedSize, classify_eq element]
      cases element.fixedSize <;> rfl
    | container names fields =>
      exact classifyFields_eq fields
    | progressiveContainer active names fields =>
      exact classifyFields_eq fields
    | _ => rfl

  theorem classifyFields_eq (fields : List Ssz.Desc) :
      classifyFields fields = (Ssz.Desc.fieldsFixedSize fields).isSome := by
    cases fields with
    | nil => rfl
    | cons field rest =>
      simp only [classifyFields, Ssz.Desc.fieldsFixedSize,
        classify_eq field, classifyFields_eq rest]
      cases field.fixedSize <;> cases Ssz.Desc.fieldsFixedSize rest <;> rfl
end

/-- The allocation-free classifier agrees with the pinned upstream query. -/
theorem classify_isFixed (desc : Ssz.Desc) :
    classify desc = desc.isFixed := classify_eq desc

/-- A negative classification determines the answer before measuring any field. -/
theorem variable_width (desc : Ssz.Desc) (h : classify desc = false) :
    desc.fixedSize = none := by
  rw [classify_eq] at h
  cases he : desc.fixedSize <;> simp_all

/- The measurement model uses exact natural arithmetic for the native limb
operations. Arena exhaustion and the machine implementation of that arithmetic
are separate obligations; no resource-success claim is made here. -/
mutual
  def measure : Ssz.Desc → Option Nat
    | .bool => some 1
    | .uint width => some width
    | .byteVector length => some length
    | .bitVector length =>
      some (length / 8 + if length % 8 = 0 then 0 else 1)
    | .vector element length => (measure element).map (· * length)
    | .container _ fields | .progressiveContainer _ _ fields =>
      measureFields fields 0
    | _ => none

  def measureFields : List Ssz.Desc → Nat → Option Nat
    | [], total => some total
    | field :: rest, total =>
      match measure field with
      | none => none
      | some width => measureFields rest (total + width)
end

mutual
  theorem measure_eq (desc : Ssz.Desc) : measure desc = desc.fixedSize := by
    cases desc with
    | bitVector length =>
      simp only [measure, Ssz.Desc.fixedSize]
      congr 1
      split <;> omega
    | vector element length =>
      simp only [measure, Ssz.Desc.fixedSize, measure_eq element]
    | container names fields =>
      simpa [measure, Ssz.Desc.fixedSize] using measureFields_eq fields 0
    | progressiveContainer active names fields =>
      simpa [measure, Ssz.Desc.fixedSize] using measureFields_eq fields 0
    | _ => rfl

  theorem measureFields_eq (fields : List Ssz.Desc) (total : Nat) :
      measureFields fields total =
        (Ssz.Desc.fieldsFixedSize fields).map (total + ·) := by
    cases fields with
    | nil => simp [measureFields, Ssz.Desc.fieldsFixedSize]
    | cons field rest =>
      simp only [measureFields, measure_eq field, Ssz.Desc.fieldsFixedSize]
      cases field.fixedSize with
      | none => rfl
      | some width =>
        dsimp only
        rw [measureFields_eq rest]
        cases Ssz.Desc.fieldsFixedSize rest <;> simp [Nat.add_assoc]
end

/-- The native preflight avoids measuring variable layouts. -/
def size (desc : Ssz.Desc) : Option Nat :=
  if classify desc then measure desc else none

theorem size_eq (desc : Ssz.Desc) : size desc = desc.fixedSize := by
  simp only [size, classify_eq, measure_eq]
  cases desc.fixedSize <;> rfl

end SszNative.Fixed
