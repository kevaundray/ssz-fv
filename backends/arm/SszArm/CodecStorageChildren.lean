import SszArm.CodecStorageProjection

namespace SszArm.Codec.Storage

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure (Plan)
open SszNative.CodecDecode (Node)

/-- The same child witness serves both unprotected and framed callers. -/
theorem vector_child {protect s address child count}
    (input : (desc address (.vector child count)).Holds protect s) :
    ∃ pointer, (Image.word (address + 24) 8 pointer).Holds protect s ∧
      (desc pointer child).Holds protect s := input.2.2.2

theorem list_child {protect s address child count}
    (input : (desc address (.list child count)).Holds protect s) :
    ∃ pointer, (Image.word (address + 24) 8 pointer).Holds protect s ∧
      (desc pointer child).Holds protect s := input.2.2.2

theorem progressiveList_child {protect s address child limit}
    (input : (desc address (.progressiveList child limit)).Holds protect s) :
    ∃ pointer, (Image.word (address + 8) 8 pointer).Holds protect s ∧
      (desc pointer child).Holds protect s := input.2.2.2

theorem container_fields {protect s address fields}
    (input : (desc address (.container fields)).Holds protect s) :
    ∃ pointer, (Image.word (address + 8) 8 pointer).Holds protect s ∧
      (Image.word (address + 16) 8 fields.length).Holds protect s ∧
      Physical pointer (fields.length * 24) 8 ∧
      (fieldEntries pointer fields).Holds protect s := input.2.2

theorem progressiveContainer_fields {protect s address active fields}
    (input : (desc address (.progressiveContainer active fields)).Holds protect s) :
    ∃ pointer, (Image.word (address + 24) 8 pointer).Holds protect s ∧
      (Image.word (address + 32) 8 fields.length).Holds protect s ∧
      Physical pointer (fields.length * 24) 8 ∧
      (fieldEntries pointer fields).Holds protect s := input.2.2.2

theorem compatibleUnion_variants {protect s address variants}
    (input : (desc address (.compatibleUnion variants)).Holds protect s) :
    ∃ pointer, (Image.word (address + 8) 8 pointer).Holds protect s ∧
      (Image.word (address + 16) 8 variants.length).Holds protect s ∧
      Physical pointer (variants.length * 24) 8 ∧
      (variantEntries pointer variants).Holds protect s := input.2.2

theorem field_child {protect s address name shape rest}
    (input : (fieldEntries address ((name, shape) :: rest)).Holds protect s) :
    ∃ pointer, (Image.word (address + 16) 8 pointer).Holds protect s ∧
      (desc pointer shape).Holds protect s := input.1.2.2

theorem variant_child {protect s address selector shape rest}
    (input : (variantEntries address ((selector, shape) :: rest)).Holds protect s) :
    ∃ pointer, (Image.word address 8 pointer).Holds protect s ∧
      (desc pointer shape).Holds protect s := input.1.2.2

theorem sequence_children {protect s address children}
    (input : (value address (.seq children)).Holds protect s) :
    ∃ pointer, (Image.word (address + 8) 8 pointer).Holds protect s ∧
      (Image.word (address + 16) 8 children.length).Holds protect s ∧
      Physical pointer (children.length * 48) 16 ∧
      (valueEntries pointer children).Holds protect s := input.2.2

theorem union_child {protect s address selector child}
    (input : (value address (.union selector child)).Holds protect s) :
    ∃ pointer, (Image.word (address + 24) 8 pointer).Holds protect s ∧
      (value pointer child).Holds protect s := input.2.2.2

theorem plan_children {protect s address logical}
    (input : (plan address logical).Holds protect s) :
    Physical logical.childrenPointer (logical.children.length * 40) 8 ∧
      (planEntries logical.childrenPointer logical.children).Holds protect s := by
  cases logical with
  | mk size leading children allocation => exact input.2.2.2.2.2.2

theorem prefix_get {α : Type} (entry : Nat → α → Image) (stride : Nat)
    {protect s address values index selected}
    (input : (entries entry stride address values).Holds protect s)
    (found : values[index]? = some selected) :
    (entry (address + stride * index) selected).Holds protect s := by
  induction values generalizing address index with
  | nil => simp at found
  | cons first rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst selected
          simpa only [Nat.mul_zero, Nat.add_zero] using input.1
      | succ index =>
          have result := ih (address := address + stride) input.2 found
          simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

theorem valueEntries_prefix (address : Nat) (children : List Value) :
    valueEntries address children = entries value 48 address children := by
  induction children generalizing address with
  | nil => rfl
  | cons child rest ih => simp only [valueEntries, entries, ih]

theorem planEntries_prefix (address : Nat) (children : List Plan) :
    planEntries address children = entries plan 40 address children := by
  induction children generalizing address with
  | nil => rfl
  | cons child rest ih => simp only [planEntries, entries, ih]

theorem nodeEntries_prefix (inputBase address : Nat) (children : List Node) :
    nodeEntries inputBase address children = entries (node inputBase) 48 address children := by
  induction children generalizing address with
  | nil => rfl
  | cons child rest ih => simp only [nodeEntries, entries, ih]

end SszArm.Codec.Storage
