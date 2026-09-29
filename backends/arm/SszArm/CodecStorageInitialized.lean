import SszArm.CodecStorageDecoded

namespace SszArm.Codec.Storage

/-- Concatenation composes meaningful observations, not byte copies of padding. -/
theorem entries_append {α : Type} (entry : Nat → α → Image) (stride : Nat)
    (left right : List α) (address : Nat) (protect : Nat → Nat → Prop) (s : ArmState) :
    (entries entry stride address (left ++ right)).Holds protect s ↔
      (entries entry stride address left).Holds protect s ∧
      (entries entry stride (address + stride * left.length) right).Holds protect s := by
  induction left generalizing address with
  | nil => simp only [List.nil_append, entries, Image.Holds, List.length_nil,
      Nat.mul_zero, Nat.add_zero, true_and]
  | cons first rest ih =>
      simp only [List.cons_append, entries, Image.Holds, ih, List.length_cons,
        Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, and_assoc]

/-- Extending the logical initialized prefix does not assert anything about the
uninitialized reservation suffix or about bytes between meaningful fields. -/
theorem initializedPrefix_append {α : Type} (entry : Nat → α → Image)
    {protect s address count stride alignment initialized suffix}
    (before : (initializedPrefix entry address count stride alignment initialized).Holds protect s)
    (added : (entries entry stride (address + stride * initialized.length) suffix).Holds protect s)
    (fits : (initialized ++ suffix).length ≤ count) :
    (initializedPrefix entry address count stride alignment (initialized ++ suffix)).Holds protect s :=
  ⟨before.1, fits,
    (entries_append entry stride initialized suffix address protect s).2 ⟨before.2.2, added⟩⟩

/-- Reservation does not require even the first slot to be initialized. This is
also the representation at an allocator commit followed by initializer failure. -/
theorem initializedPrefix_empty {α : Type} (entry : Nat → α → Image)
    {protect s address count stride alignment}
    (physical : Physical address (count * stride) alignment) :
    (initializedPrefix entry address count stride alignment []).Holds protect s :=
  ⟨physical, Nat.zero_le count, True.intro⟩

end SszArm.Codec.Storage
