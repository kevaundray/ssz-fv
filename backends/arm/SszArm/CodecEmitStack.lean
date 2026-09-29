import SszArm.CodecFixedStack
import SszArm.CodecStack
import SszCodecEmitPlans

namespace SszArm.Codec.Emit

open SszNative.Codec (Desc)
open SszNative.CodecMeasure (Parts)

mutual
/-- Stack storage for the actual 160-byte emit activation, its 16-byte
lowering slots, and all recursively reached callees. A sibling returns before
its successor starts, so array lengths do not multiply stack consumption. -/
def stackBytes : Desc → Nat
  | .primitive _ => 176
  | .vector child _ | .list child _ | .progressiveList child _ =>
      160 + (224 + max 16 (stackBytes child))
  | .container fields | .progressiveContainer _ fields =>
      160 + (224 + max 16 (max (fieldsStackBytes fields) (Fixed.isFixedFieldsStack fields)))
  | .compatibleUnion variants => 160 + max 16 (variantsStackBytes variants)

def fieldsStackBytes : List (String × Desc) → Nat
  | [] => 0
  | (_, child) :: rest => max (stackBytes child) (fieldsStackBytes rest)

def variantsStackBytes : List (SszNative.NatOperand × Desc) → Nat
  | [] => 0
  | (_, child) :: rest => max (stackBytes child) (variantsStackBytes rest)
end

/-- emit_parts has a 224-byte frame. Its host-size scan uses one 16-byte
lowering slot; retained fields also call the actual recursive is_fixed helper.
Neither memcpy nor Nat.compare increases this bound beyond that lowering slot. -/
def partsStackBytes : Parts → Nat
  | .repeated child => 224 + max 16 (stackBytes child)
  | .fields fields =>
      224 + max 16 (max (fieldsStackBytes fields) (Fixed.isFixedFieldsStack fields))

theorem stackBytes_activation (desc : Desc) : 176 ≤ stackBytes desc := by
  cases desc <;> simp only [stackBytes] <;> omega

theorem partsStackBytes_activation (parts : Parts) : 240 ≤ partsStackBytes parts := by
  cases parts <;> simp only [partsStackBytes] <;> omega

theorem fieldsStackBytes_member (fields : List (String × Desc))
    (name : String) (child : Desc) (member : (name, child) ∈ fields) :
    stackBytes child ≤ fieldsStackBytes fields := by
  induction fields with
  | nil => cases member
  | cons field rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst field
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

theorem variantsStackBytes_member (variants : List (SszNative.NatOperand × Desc))
    (selector : SszNative.NatOperand) (child : Desc) (member : (selector, child) ∈ variants) :
    stackBytes child ≤ variantsStackBytes variants := by
  induction variants with
  | nil => cases member
  | cons variant rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst variant
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

theorem repeated_stack (child : Desc) :
    224 + stackBytes child ≤ partsStackBytes (.repeated child) := by
  simp only [partsStackBytes]
  omega

theorem field_stack (fields : List (String × Desc)) (name : String) (child : Desc)
    (member : (name, child) ∈ fields) :
    224 + stackBytes child ≤ partsStackBytes (.fields fields) := by
  have childBound := fieldsStackBytes_member fields name child member
  simp only [partsStackBytes]
  omega

theorem fixed_field_stack (fields : List (String × Desc)) (name : String) (child : Desc)
    (member : (name, child) ∈ fields) :
    224 + Fixed.isFixedStack child ≤ partsStackBytes (.fields fields) := by
  have childBound : Fixed.isFixedStack child ≤ Fixed.isFixedFieldsStack fields := by
    induction fields with
    | nil => cases member
    | cons field rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst field
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)
  simp only [partsStackBytes]
  omega

theorem composite_stack (desc : Desc) (parts : Parts)
    (shape : SszNative.CodecEmit.Composite desc parts) :
    160 + partsStackBytes parts = stackBytes desc := by
  cases shape <;> rfl

theorem union_stack (variants : List (SszNative.NatOperand × Desc))
    (selector : SszNative.NatOperand) (child : Desc) (member : (selector, child) ∈ variants) :
    160 + stackBytes child ≤ stackBytes (.compatibleUnion variants) := by
  have childBound := variantsStackBytes_member variants selector child member
  simp only [stackBytes]
  omega

/-- First-match selection never escapes the original variant slice, including
noncanonical selector operands and duplicate numerical selectors. -/
theorem selected_member (variants : List (SszNative.NatOperand × Desc))
    (selector : SszNative.NatOperand) (child : Desc)
    (selected : SszNative.CodecMeasure.option variants selector = .ok child) :
    ∃ stored, (stored, child) ∈ variants := by
  induction variants with
  | nil => cases selected
  | cons variant rest ih =>
    rcases variant with ⟨stored, desc⟩
    simp only [SszNative.CodecMeasure.option] at selected
    split at selected
    · have same := Except.ok.inj selected
      subst desc
      exact ⟨stored, by simp⟩
    · obtain ⟨stored, member⟩ := ih selected
      exact ⟨stored, List.mem_cons_of_mem _ member⟩

theorem selected_stack (variants : List (SszNative.NatOperand × Desc))
    (selector : SszNative.NatOperand) (child : Desc)
    (selected : SszNative.CodecMeasure.option variants selector = .ok child) :
    160 + stackBytes child ≤ stackBytes (.compatibleUnion variants) := by
  obtain ⟨stored, member⟩ := selected_member variants selector child selected
  exact union_stack variants stored child member

theorem selected_nesting (variants : List (SszNative.NatOperand × Desc))
    (selector : SszNative.NatOperand) (child : Desc)
    (selected : SszNative.CodecMeasure.option variants selector = .ok child) :
    child.nesting < (Desc.compatibleUnion variants).nesting := by
  obtain ⟨stored, member⟩ := selected_member variants selector child selected
  apply Desc.child_nesting_lt
  exact List.mem_map.mpr ⟨(stored, child), member, rfl⟩

end SszArm.Codec.Emit
