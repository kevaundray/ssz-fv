import SszArm.CodecStorageChildren

namespace SszArm.Codec.Storage

open SszNative.CodecDecode (Node)

 theorem node_values_length (children : List Node) : Node.values children |>.length = children.length := by
  induction children with
  | nil => rfl
  | cons child rest ih => simp only [Node.values, List.length_cons, ih]

mutual
  theorem node_value {protect s inputBase address} (logical : Node)
      (input : (node inputBase address logical).Holds protect s) :
      (value address logical.value).Holds protect s := by
    cases logical with
    | bool flag => exact input
    | uint number => exact input
    | bytes offset data =>
        exact ⟨input.1, input.2.1, inputBase + offset,
          input.2.2.1, input.2.2.2.1, input.2.2.2.2⟩
    | bits offset data =>
        exact ⟨input.1, input.2.1,
          ⟨inputBase + offset, input.2.2.1, input.2.2.2.1,
            input.2.2.2.2.1, input.2.2.2.2.2.1⟩,
          input.2.2.2.2.2.2⟩
    | seq allocation children =>
        refine ⟨input.1, input.2.1, nodePointer allocation, input.2.2.1, ?_, ?_, ?_⟩
        · simpa only [node_values_length] using input.2.2.2.1
        · simpa only [node_values_length] using input.2.2.2.2.2.1
        · exact node_values children input.2.2.2.2.2.2
    | union selector allocation child =>
        exact ⟨input.1, input.2.1, input.2.2.1, allocation.pointer,
          input.2.2.2.1, node_value child input.2.2.2.2⟩

  theorem node_values {protect s inputBase address} (children : List Node)
      (input : (nodeEntries inputBase address children).Holds protect s) :
      (valueEntries address (Node.values children)).Holds protect s := by
    cases children with
    | nil => trivial
    | cons child rest => exact ⟨node_value child input.1, node_values rest input.2⟩
end

 theorem decoded_value {s inputBase address logical}
    (input : NodeAt s inputBase address logical) : ValueAt s address logical.value :=
  node_value logical input

 theorem decoded_value_owned {writes s inputBase address logical}
    (input : NodeOwned writes s inputBase address logical) :
    ValueOwned writes s address logical.value := node_value logical input

 theorem initializedPrefix_entry {α : Type} (entry : Nat → α → Image)
    {protect s address count stride alignment initialized index selected}
    (input : (initializedPrefix entry address count stride alignment initialized).Holds protect s)
    (found : initialized[index]? = some selected) :
    (entry (address + stride * index) selected).Holds protect s :=
  prefix_get entry stride input.2.2 found

 theorem initializedPrefix_count {α : Type} (entry : Nat → α → Image)
    {protect s address count stride alignment initialized}
    (input : (initializedPrefix entry address count stride alignment initialized).Holds protect s) :
    initialized.length ≤ count := input.2.1

 theorem initializedPrefix_preserved {α : Type} (entry : Nat → α → Image)
    {writes s t address count stride alignment initialized}
    (input : (initializedPrefix entry address count stride alignment initialized).Owned writes s)
    (frame : Delimited.MemoryFrame writes s t) :
    (initializedPrefix entry address count stride alignment initialized).Owned writes t :=
  Image.preserved _ frame input

end SszArm.Codec.Storage
