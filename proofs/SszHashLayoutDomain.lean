import SszHashLayoutNested

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

mutual
/-- Only the native basic-width restriction; capacities and selectors stay raw. -/
def SafeWidths : Desc → Prop
  | .primitive (.uint width) => width.value ≤ 32
  | .primitive _ => True
  | .vector element _ | .list element _ | .progressiveList element _ => SafeWidths element
  | .container fields | .progressiveContainer _ fields => fieldsSafeWidths fields
  | .compatibleUnion variants => variantsSafeWidths variants

def fieldsSafeWidths : List (String × Desc) → Prop
  | [] => True
  | (_, desc) :: rest => SafeWidths desc ∧ fieldsSafeWidths rest

def variantsSafeWidths : List (NatOperand × Desc) → Prop
  | [] => True
  | (_, desc) :: rest => SafeWidths desc ∧ variantsSafeWidths rest
end

@[simp] theorem SafeWidths.uint_iff (width : NatOperand) :
    SafeWidths (.primitive (.uint width)) ↔ width.value ≤ 32 := Iff.rfl

/-- Every SSZ integer width discharges the only extra native declaration bound. -/
theorem SafeWidths.uint_of_supported (width : NatOperand)
    (supported : width.value ∈ [1, 2, 4, 8, 16, 32]) :
    SafeWidths (.primitive (.uint width)) := by
  change width.value ≤ 32
  simp at supported
  omega

theorem fieldsSafeWidths_iff (fields : List (String × Desc)) :
    fieldsSafeWidths fields ↔ ∀ field ∈ fields, SafeWidths field.2 := by
  induction fields with
  | nil => simp [fieldsSafeWidths]
  | cons field rest ih => cases field; simp [fieldsSafeWidths, ih]

theorem variantsSafeWidths_iff (variants : List (NatOperand × Desc)) :
    variantsSafeWidths variants ↔ ∀ variant ∈ variants, SafeWidths variant.2 := by
  induction variants with
  | nil => simp [variantsSafeWidths]
  | cons variant rest ih => cases variant; simp [variantsSafeWidths, ih]

theorem SafeWidths.child {parent child : Desc} (safe : SafeWidths parent)
    (member : child ∈ parent.children) : SafeWidths child := by
  cases parent with
  | primitive shape => simp [Desc.children] at member
  | vector element length | list element length | progressiveList element length =>
    have same : child = element := by simpa [Desc.children] using member
    subst child
    exact safe
  | container fields | progressiveContainer active fields =>
    rcases List.mem_map.mp member with ⟨field, inside, same⟩
    rw [← same]
    exact (fieldsSafeWidths_iff fields).mp safe field inside
  | compatibleUnion variants =>
    rcases List.mem_map.mp member with ⟨variant, inside, same⟩
    rw [← same]
    exact (variantsSafeWidths_iff variants).mp safe variant inside

/-- Reflexive descendant relation; no validity, execution, or fuel premise. -/
inductive Descendant : Desc → Desc → Prop where
  | self (desc : Desc) : Descendant desc desc
  | step {parent child next : Desc} (member : child ∈ parent.children)
      (rest : Descendant child next) : Descendant parent next

theorem SafeWidths.descendant {parent child : Desc} (safe : SafeWidths parent)
    (below : Descendant parent child) : SafeWidths child := by
  induction below with
  | self => exact safe
  | step member rest ih => exact ih (safe.child member)

theorem Descendant.physical {parent child : Desc} (below : Descendant parent child)
    (physical : parent.Physical) : child.Physical := by
  induction below with
  | self => exact physical
  | step member rest ih => exact ih (Desc.physical_child _ _ physical member)

theorem lookup_member {variants : List (NatOperand × Desc)} {selector : NatOperand}
    {desc : Desc} (selected : lookup variants selector = some desc) :
    desc ∈ variants.map Prod.snd := by
  induction variants with
  | nil => simp [lookup] at selected
  | cons variant rest ih =>
    rcases variant with ⟨chosen, option⟩
    simp only [lookup] at selected
    split at selected
    · cases selected
      simp
    · exact List.mem_cons_of_mem _ (ih selected)

private theorem fields_at_members {fields : List (String × Desc)} {values : List Value}
    {index : Nat} {desc : Desc} {value : Value}
    (selected : (Nested.fields fields values).at index = some (desc, value)) :
    desc ∈ fields.map Prod.snd ∧ value ∈ values := by
  simp only [Nested.at] at selected
  cases hf : fields[index]? with
  | none => simp [hf] at selected
  | some field =>
    cases hv : values[index]? with
    | none => simp [hf, hv] at selected
    | some item =>
      have same : (field.2, item) = (desc, value) := by simpa [hf, hv] using selected
      cases same
      exact ⟨List.mem_map.mpr ⟨field, List.mem_of_getElem? hf, rfl⟩,
        List.mem_of_getElem? hv⟩

theorem Generated.at_children {parent : Desc} {input : Value} {nested : Nested}
    (generated : Generated parent input nested) {index : Nat} {desc : Desc} {value : Value}
    (selected : nested.at index = some (desc, value)) :
    desc ∈ parent.children ∧ value ∈ input.children := by
  cases generated with
  | vector element length values | list element length values | progressiveList element length values =>
    cases hv : values[index]? with
    | none => simp [Nested.at, hv] at selected
    | some item =>
      have same : (element, item) = (desc, value) := by simpa [Nested.at, hv] using selected
      cases same
      exact ⟨by simp [Desc.children], List.mem_of_getElem? hv⟩
  | container fields values => exact fields_at_members selected
  | progressiveContainer active fields values =>
    simp only [Nested.at] at selected
    split at selected
    · exact fields_at_members selected
    · cases selected
  | compatibleUnion variants selector option item found =>
    simp only [Nested.at] at selected
    split at selected
    · have same : (option, item) = (desc, value) := Option.some.inj selected
      cases same
      exact ⟨lookup_member found, by simp [Value.children]⟩
    · cases selected

theorem Generated.at_child {parent : Desc} {input : Value} {nested : Nested}
    (generated : Generated parent input nested) {index : Nat} {desc : Desc} {value : Value}
    (selected : nested.at index = some (desc, value)) : value ∈ input.children :=
  (generated.at_children selected).2

theorem Generated.at_desc_child {parent : Desc} {input : Value} {nested : Nested}
    (generated : Generated parent input nested) {index : Nat} {desc : Desc} {value : Value}
    (selected : nested.at index = some (desc, value)) : desc ∈ parent.children :=
  (generated.at_children selected).1

theorem Generated.at_nesting_lt {parent : Desc} {input : Value} {nested : Nested}
    (generated : Generated parent input nested) {index : Nat} {desc : Desc} {value : Value}
    (selected : nested.at index = some (desc, value)) : desc.nesting < parent.nesting :=
  Desc.child_nesting_lt parent desc (generated.at_desc_child selected)

theorem Generated.at_value_nesting_lt {parent : Desc} {input : Value} {nested : Nested}
    (generated : Generated parent input nested) {index : Nat} {desc : Desc} {value : Value}
    (selected : nested.at index = some (desc, value)) : value.nesting < input.nesting :=
  Value.child_nesting_lt input value (generated.at_child selected)

theorem Generated.at_safeWidths {parent : Desc} {input : Value} {nested : Nested}
    (generated : Generated parent input nested) (safe : SafeWidths parent)
    {index : Nat} {desc : Desc} {value : Value}
    (selected : nested.at index = some (desc, value)) : SafeWidths desc :=
  safe.child (generated.at_desc_child selected)

theorem Generated.at_physical {parent : Desc} {input : Value} {nested : Nested}
    (generated : Generated parent input nested) (descPhysical : parent.Physical)
    (valuePhysical : input.Physical) {index : Nat} {desc : Desc} {value : Value}
    (selected : nested.at index = some (desc, value)) : desc.Physical ∧ value.Physical :=
  ⟨Desc.physical_child parent desc descPhysical (generated.at_desc_child selected),
   Value.physical_child input value valuePhysical (generated.at_child selected)⟩

/-- Physical slice bounds cover the native traversal counter, not logical limits. -/
theorem Generated.count_physical {parent : Desc} {input : Value} {nested : Nested}
    (generated : Generated parent input nested) (descPhysical : parent.Physical)
    (valuePhysical : input.Physical) : nested.count < 2 ^ 64 := by
  cases generated with
  | vector element length values | list element length values | progressiveList element length values | container fields values =>
    exact valuePhysical.1
  | progressiveContainer active fields values => exact descPhysical.1
  | compatibleUnion variants selector desc value selected =>
    change 1 < 2 ^ 64
    decide

end SszNative.HashLayout
