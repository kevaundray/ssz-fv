import SszCodecTypes

set_option autoImplicit false

namespace SszNative.Codec

@[simp] theorem Desc.erase_primitive (shape : Serialize.Desc) :
    (Desc.primitive shape).erase = shape.erase := rfl

@[simp] theorem Desc.erase_vector (element : Desc) (length : NatOperand) :
    (Desc.vector element length).erase = .vector element.erase length.value := rfl

@[simp] theorem Desc.erase_list (element : Desc) (limit : NatOperand) :
    (Desc.list element limit).erase = .list element.erase limit.value := rfl

@[simp] theorem Desc.erase_progressiveList (element : Desc) (limit : Option NatOperand) :
    (Desc.progressiveList element limit).erase =
      .progressiveList element.erase (limit.map NatOperand.value) := rfl

@[simp] theorem Desc.erase_container (fields : List (String × Desc)) :
    (Desc.container fields).erase = .container (fields.map Prod.fst) (Desc.eraseFields fields) := rfl

@[simp] theorem Desc.erase_progressiveContainer (active : List Bool)
    (fields : List (String × Desc)) :
    (Desc.progressiveContainer active fields).erase =
      .progressiveContainer active (fields.map Prod.fst) (Desc.eraseFields fields) := rfl

@[simp] theorem Desc.erase_compatibleUnion (variants : List (NatOperand × Desc)) :
    (Desc.compatibleUnion variants).erase =
      .compatibleUnion (variants.map (fun variant => variant.1.value))
        (Desc.eraseVariants variants) := rfl

/-- Erasure preserves every field's position, including duplicate names. -/
theorem Desc.eraseFields_eq_map (fields : List (String × Desc)) :
    Desc.eraseFields fields = fields.map (fun field => field.2.erase) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    rcases field with ⟨name, shape⟩
    simp only [Desc.eraseFields, List.map_cons, ih]

/-- Erasure preserves every variant's position, including duplicate selectors. -/
theorem Desc.eraseVariants_eq_map (variants : List (NatOperand × Desc)) :
    Desc.eraseVariants variants = variants.map (fun variant => variant.2.erase) := by
  induction variants with
  | nil => rfl
  | cons variant rest ih =>
    rcases variant with ⟨selector, shape⟩
    simp only [Desc.eraseVariants, List.map_cons, ih]

@[simp] theorem Desc.eraseFields_length (fields : List (String × Desc)) :
    (Desc.eraseFields fields).length = fields.length := by
  simp [Desc.eraseFields_eq_map]

@[simp] theorem Desc.eraseVariants_length (variants : List (NatOperand × Desc)) :
    (Desc.eraseVariants variants).length = variants.length := by
  simp [Desc.eraseVariants_eq_map]

/-- Splitting native field pairs cannot misassociate a name with its type. -/
theorem Desc.eraseFields_zip (fields : List (String × Desc)) :
    (fields.map Prod.fst).zip (Desc.eraseFields fields) =
      fields.map (fun field => (field.1, field.2.erase)) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    rcases field with ⟨name, shape⟩
    simp [Desc.eraseFields, ih]

/-- Splitting variants cannot misassociate a selector with its option. -/
theorem Desc.eraseVariants_zip (variants : List (NatOperand × Desc)) :
    (variants.map (fun variant => variant.1.value)).zip (Desc.eraseVariants variants) =
      variants.map (fun variant => (variant.1.value, variant.2.erase)) := by
  induction variants with
  | nil => rfl
  | cons variant rest ih =>
    rcases variant with ⟨selector, shape⟩
    simp [Desc.eraseVariants, ih]

@[simp] theorem Value.erase_bool (value : Bool) :
    (Value.bool value).erase = .bool value := rfl

@[simp] theorem Value.erase_uint (number : NatOperand) :
    (Value.uint number).erase = .uint number.value := rfl

@[simp] theorem Value.erase_bytes (data : Ssz.Bytes) :
    (Value.bytes data).erase = .bytes data := rfl

@[simp] theorem Value.erase_bits (data : Serialize.Packed) :
    (Value.bits data).erase = .bits (Ssz.unpackBits data.bytes data.count.toNat) := rfl

@[simp] theorem Value.erase_seq (values : List Value) :
    (Value.seq values).erase = .seq (Value.eraseList values) := rfl

@[simp] theorem Value.erase_union (selector : NatOperand) (value : Value) :
    (Value.union selector value).erase = .union selector.value value.erase := rfl

theorem Value.eraseList_eq_map (values : List Value) :
    Value.eraseList values = values.map Value.erase := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp only [Value.eraseList, List.map_cons, ih]

@[simp] theorem Value.eraseList_length (values : List Value) :
    (Value.eraseList values).length = values.length := by
  simp [Value.eraseList_eq_map]

@[simp] theorem Value.toPrimitive_bool (value : Bool) :
    (Value.bool value).toPrimitive = .bool value := rfl

@[simp] theorem Value.toPrimitive_uint (number : NatOperand) :
    (Value.uint number).toPrimitive = .uint number := rfl

@[simp] theorem Value.toPrimitive_bytes (data : Ssz.Bytes) :
    (Value.bytes data).toPrimitive = .bytes data := rfl

@[simp] theorem Value.toPrimitive_bits (data : Serialize.Packed) :
    (Value.bits data).toPrimitive = .bits data := rfl

@[simp] theorem Value.toPrimitive_seq (values : List Value) :
    (Value.seq values).toPrimitive = .seq (Value.eraseList values) := rfl

@[simp] theorem Value.toPrimitive_union (selector : NatOperand) (value : Value) :
    (Value.union selector value).toPrimitive = .union selector value.erase := rfl

/-- Primitive projection and total recursive erasure agree for every raw value,
not only for well-typed values or for values accepted by a primitive codec. -/
@[simp] theorem Value.erase_toPrimitive (value : Value) :
    value.toPrimitive.erase = value.erase := by
  cases value <;> rfl

@[simp] theorem Desc.erase_tag (shape : Desc) :
    erasedDescTag shape.erase = shape.tag := by
  cases shape with
  | primitive shape => cases shape <;> rfl
  | _ => rfl

@[simp] theorem Value.erase_tag (value : Value) :
    erasedValueTag value.erase = value.tag := by
  cases value <;> rfl

@[simp] theorem Value.toPrimitive_tag (value : Value) :
    primitiveValueTag value.toPrimitive = value.tag := by
  cases value <;> rfl

/-- Composite wrong-kind reuse is exact, including the unchanged cursor and
empty arithmetic-call history, regardless of any child's validity. -/
theorem primitive_measure_seq (shape : Serialize.Desc) (values : List Value)
    (arena : Delimited.ArenaState) :
    Serialize.measure shape (Value.seq values).toPrimitive arena =
      Serialize.unchanged arena.used (.error .wrongType) := by
  cases shape <;> rfl

theorem primitive_measure_union (shape : Serialize.Desc) (selector : NatOperand)
    (value : Value) (arena : Delimited.ArenaState) :
    Serialize.measure shape (Value.union selector value).toPrimitive arena =
      Serialize.unchanged arena.used (.error .wrongType) := by
  cases shape <;> rfl

/-- The recursive physical predicate is sufficient for every existing primitive
physical precondition; no logical Nat bound is introduced by this bridge. -/
theorem Value.physical_toPrimitive (value : Value) (physical : value.Physical) :
    value.toPrimitive.Physical := by
  cases value <;>
    simp_all [Value.Physical, Value.toPrimitive, Serialize.Value.Physical]

theorem Desc.fieldsPhysical_iff (fields : List (String × Desc)) :
    Desc.fieldsPhysical fields ↔
      ∀ field ∈ fields, field.1.toUTF8.size < 2 ^ 64 ∧ field.2.Physical := by
  induction fields with
  | nil => simp [Desc.fieldsPhysical]
  | cons field rest ih =>
    rcases field with ⟨name, shape⟩
    simp [Desc.fieldsPhysical, ih, and_assoc]

theorem Desc.variantsPhysical_iff (variants : List (NatOperand × Desc)) :
    Desc.variantsPhysical variants ↔
      ∀ variant ∈ variants, operandSliceSized variant.1 ∧ variant.2.Physical := by
  induction variants with
  | nil => simp [Desc.variantsPhysical]
  | cons variant rest ih =>
    rcases variant with ⟨selector, shape⟩
    simp [Desc.variantsPhysical, ih, and_assoc]

theorem Value.listPhysical_iff (values : List Value) :
    Value.listPhysical values ↔ ∀ value ∈ values, value.Physical := by
  induction values with
  | nil => simp [Value.listPhysical]
  | cons value rest ih => simp [Value.listPhysical, ih]

/-- A borrowed subtree has the same optional physical slice-size obligations
whether visited through one parent or through several shared references. -/
theorem Desc.physical_child (parent child : Desc) (physical : parent.Physical)
    (member : child ∈ parent.children) : child.Physical := by
  cases parent with
  | primitive shape => simp [Desc.children] at member
  | vector element length | list element length | progressiveList element length =>
    have same : child = element := by simpa [Desc.children] using member
    subst child
    exact physical.1
  | container fields =>
    rcases List.mem_map.mp member with ⟨field, inside, same⟩
    rw [← same]
    exact ((Desc.fieldsPhysical_iff fields).mp physical.2 field inside).2
  | progressiveContainer active fields =>
    rcases List.mem_map.mp member with ⟨field, inside, same⟩
    rw [← same]
    exact ((Desc.fieldsPhysical_iff fields).mp physical.2.2 field inside).2
  | compatibleUnion variants =>
    rcases List.mem_map.mp member with ⟨variant, inside, same⟩
    rw [← same]
    exact ((Desc.variantsPhysical_iff variants).mp physical.2 variant inside).2

theorem Value.physical_child (parent child : Value) (physical : parent.Physical)
    (member : child ∈ parent.children) : child.Physical := by
  cases parent with
  | seq values => exact (Value.listPhysical_iff values).mp physical.2 child member
  | union selector value =>
    have same : child = value := by simpa [Value.children] using member
    subst child
    exact physical.2
  | _ => simp [Value.children] at member

/-- Type depth agrees with upstream for all raw declarations, without validating
names, active-field masks, selectors, capacities, or integer widths. -/
@[simp] theorem Desc.erase_nesting (shape : Desc) : shape.erase.nesting = shape.nesting := rfl

@[simp] theorem Desc.nesting_primitive (shape : Serialize.Desc) :
    (Desc.primitive shape).nesting = 1 := by
  cases shape <;> rfl

theorem Desc.nesting_pos (shape : Desc) : 0 < shape.nesting := by
  cases shape with
  | primitive shape => cases shape <;> exact Nat.zero_lt_succ _
  | _ => exact Nat.zero_lt_succ _

private theorem nesting_le_deepest (shape : Ssz.Desc) (fields : List Ssz.Desc)
    (member : shape ∈ fields) : shape.nesting ≤ Ssz.Desc.deepestNesting fields := by
  induction fields with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | inside
    · subst shape
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih inside) (Nat.le_max_right _ _)

theorem Desc.mem_eraseFields (fields : List (String × Desc)) (child : Desc)
    (member : child ∈ fields.map Prod.snd) : child.erase ∈ Desc.eraseFields fields := by
  rw [Desc.eraseFields_eq_map]
  rcases List.mem_map.mp member with ⟨field, inside, same⟩
  exact List.mem_map.mpr ⟨field, inside, congrArg Desc.erase same⟩

theorem Desc.mem_eraseVariants (variants : List (NatOperand × Desc)) (child : Desc)
    (member : child ∈ variants.map Prod.snd) : child.erase ∈ Desc.eraseVariants variants := by
  rw [Desc.eraseVariants_eq_map]
  rcases List.mem_map.mp member with ⟨variant, inside, same⟩
  exact List.mem_map.mpr ⟨variant, inside, congrArg Desc.erase same⟩

/-- Every direct descriptor descent strictly decreases the upstream nesting
measure, even when a schema is invalid or contains duplicate/shared children. -/
theorem Desc.child_nesting_lt (parent child : Desc) (member : child ∈ parent.children) :
    child.nesting < parent.nesting := by
  cases parent with
  | primitive shape => simp [Desc.children] at member
  | vector element length | list element length | progressiveList element length =>
    have same : child = element := by simpa [Desc.children] using member
    subst child
    exact Nat.lt_succ_self _
  | container fields =>
    exact Nat.lt_succ_of_le
      (nesting_le_deepest child.erase (Desc.eraseFields fields)
        (Desc.mem_eraseFields fields child member))
  | progressiveContainer active fields =>
    exact Nat.lt_succ_of_le
      (nesting_le_deepest child.erase (Desc.eraseFields fields)
        (Desc.mem_eraseFields fields child member))
  | compatibleUnion variants =>
    exact Nat.lt_succ_of_le
      (nesting_le_deepest child.erase (Desc.eraseVariants variants)
        (Desc.mem_eraseVariants variants child member))

theorem Value.nesting_pos (value : Value) : 0 < value.nesting := by
  cases value <;> exact Nat.zero_lt_succ _

theorem Value.nesting_le_deepest (value : Value) (values : List Value)
    (member : value ∈ values) : value.nesting ≤ Value.deepestNesting values := by
  induction values with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | inside
    · subst value
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih inside) (Nat.le_max_right _ _)

theorem Value.child_nesting_lt (parent child : Value) (member : child ∈ parent.children) :
    child.nesting < parent.nesting := by
  cases parent with
  | seq values => exact Nat.lt_succ_of_le (Value.nesting_le_deepest child values member)
  | union selector value =>
    have same : child = value := by simpa [Value.children] using member
    subst child
    exact Nat.lt_succ_self _
  | _ => simp [Value.children] at member

/-- Consumer-facing structural induction over all recursively borrowed types.
The children premise is membership-based, so no distinctness or ownership of
children is needed. It covers paired field and variant lists uniformly. -/
theorem Desc.inductionOnChildren (motive : Desc → Prop)
    (step : ∀ shape, (∀ child ∈ shape.children, motive child) → motive shape)
    (shape : Desc) : motive shape := by
  have all : ∀ depth (shape : Desc), shape.nesting = depth → motive shape := by
    intro depth
    induction depth using Nat.strongRecOn with
    | ind depth ih =>
      intro parent same
      apply step parent
      intro child member
      exact ih child.nesting (by rw [← same]; exact Desc.child_nesting_lt parent child member)
        child rfl
  exact all shape.nesting shape rfl

/-- Structural induction retains native operands at every recursive value node;
it does not replace nested values with their upstream erasures. -/
theorem Value.inductionOnChildren (motive : Value → Prop)
    (step : ∀ value, (∀ child ∈ value.children, motive child) → motive value)
    (value : Value) : motive value := by
  have all : ∀ depth (value : Value), value.nesting = depth → motive value := by
    intro depth
    induction depth using Nat.strongRecOn with
    | ind depth ih =>
      intro parent same
      apply step parent
      intro child member
      exact ih child.nesting (by rw [← same]; exact Value.child_nesting_lt parent child member)
        child rfl
  exact all value.nesting value rfl

end SszNative.Codec
