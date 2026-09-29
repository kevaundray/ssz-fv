import SszArm.CodecMeasureProvenanceParts

namespace SszArm.Codec.Measure.Provenance

open SszNative (NatOperand)
open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure
open Delimited (Span)

/-- These witnesses are exclusively original-state storage, not later execution
states. They retain aliasing and original noncanonical Nat representations. -/
def DescSource (writes : List Span) (s : ArmState) (shape : Desc) : Prop :=
  ∃ address, Storage.DescOwned writes s address shape

def ValueSource (writes : List Span) (s : ArmState) (logical : Value) : Prop :=
  ∃ address, Storage.ValueOwned writes s address logical

 theorem field_sources {writes s address} (fields : List (String × Desc))
    (input : (Storage.fieldEntries address fields).Owned writes s) :
    ∀ field ∈ fields, DescSource writes s field.2 := by
  induction fields generalizing address with
  | nil => simp
  | cons first rest ih =>
      intro field member
      rcases List.mem_cons.mp member with rfl | later
      · obtain ⟨pointer, _, stored⟩ := Storage.field_child input
        exact ⟨pointer, stored⟩
      · exact ih input.2 field later

 theorem variant_sources {writes s address} (variants : List (NatOperand × Desc))
    (input : (Storage.variantEntries address variants).Owned writes s) :
    ∀ variant ∈ variants, DescSource writes s variant.2 := by
  induction variants generalizing address with
  | nil => simp
  | cons first rest ih =>
      intro variant member
      rcases List.mem_cons.mp member with rfl | later
      · obtain ⟨pointer, _, stored⟩ := Storage.variant_child input
        exact ⟨pointer, stored⟩
      · exact ih input.2 variant later

 theorem value_sources {writes s address} (children : List Value)
    (input : (Storage.valueEntries address children).Owned writes s) :
    ∀ child ∈ children, ValueSource writes s child := by
  induction children generalizing address with
  | nil => simp
  | cons first rest ih =>
      intro child member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨address, input.1⟩
      · exact ih input.2 child later

 theorem child_sources {writes s logical} (input : ValueSource writes s logical) :
    ∀ child ∈ logical.children, ValueSource writes s child := by
  obtain ⟨address, stored⟩ := input
  cases logical with
  | seq children =>
      obtain ⟨pointer, _, _, _, entries⟩ := Storage.sequence_children stored
      exact value_sources children entries
  | union selector child =>
      intro logical member
      simp only [Value.children, List.mem_singleton] at member
      subst logical
      obtain ⟨pointer, _, childAt⟩ := Storage.union_child stored
      exact ⟨pointer, childAt⟩
  | _ => simp [Value.children]

 theorem option_source {writes s} (variants : List (NatOperand × Desc)) (selector : NatOperand)
    (selectorOwned : NatDivision.OperandOwned writes selector)
    (sources : ∀ variant ∈ variants, DescSource writes s variant.2) :
    ResultOwned writes (DescSource writes s) (option variants selector) := by
  induction variants with
  | nil => exact ⟨selectorOwned, True.intro⟩
  | cons variant rest ih =>
      obtain ⟨chosen, shape⟩ := variant
      unfold option
      split
      · exact sources (chosen, shape) (by simp)
      · apply ih
        intro variant member
        exact sources variant (List.mem_cons_of_mem _ member)

end SszArm.Codec.Measure.Provenance
