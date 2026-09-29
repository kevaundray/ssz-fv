import SszArm.CodecStorageProjection

set_option autoImplicit false

namespace SszArm.Codec.Measure

open SszNative.CodecMeasure (Plan)

private theorem copy_word {s : ArmState} {source destination number : Nat}
    (input : (Storage.Image.word source 8 number).At s)
    (bound : destination + 8 ≤ 2^64)
    (copied : UintCodec.widthLoad s destination 8 = UintCodec.widthLoad s source 8) :
    (Storage.Image.word destination 8 number).At s :=
  ⟨bound, trivial, copied.trans input.2.2⟩

private theorem copy_operand {s : ArmState} {source destination : Nat}
    {operand : SszNative.NatOperand}
    (input : (Storage.Image.operand source operand).At s)
    (bound : destination + 16 ≤ 2^64)
    (pointer : UintCodec.widthLoad s destination 8 = UintCodec.widthLoad s source 8)
    (payload : UintCodec.widthLoad s (destination + 8) 8 =
      UintCodec.widthLoad s (source + 8) 8) :
    (Storage.Image.operand destination operand).At s :=
  ⟨bound, trivial, input.2.2.1,
    pointer.trans input.2.2.2.1, payload.trans input.2.2.2.2.1, input.2.2.2.2.2⟩

/-- Relocating the initialized forty-byte Plan header does not relocate its
recursive child arrays or Nat backing. Their observations remain unchanged. -/
theorem plan_copy {s : ArmState} {source destination : Nat} (plan : Plan)
    (input : Storage.PlanAt s source plan) (physical : Storage.Physical destination 40 8)
    (copied : ∀ offset bytes, offset + bytes ≤ 40 →
      UintCodec.widthLoad s (destination + offset) bytes =
        UintCodec.widthLoad s (source + offset) bytes) :
    Storage.PlanAt s destination plan := by
  cases plan with
  | mk size leading children allocation =>
    refine ⟨⟨physical, trivial⟩,
      copy_word input.2.1 (by have bound := physical.2.2.1; omega) ?_,
      copy_word input.2.2.1 (by have bound := physical.2.2.1; omega) (copied 8 8 (by decide)),
      copy_operand input.2.2.2.1 (by have bound := physical.2.2.1; omega) ?_ ?_,
      copy_word input.2.2.2.2.1 (by have bound := physical.2.2.1; omega) (copied 32 8 (by decide)),
      input.2.2.2.2.2.1, input.2.2.2.2.2.2⟩
    · simpa only [Nat.add_zero] using copied 0 8 (by decide)
    · exact copied 16 8 (by decide)
    · simpa only [Nat.add_assoc] using copied 24 8 (by decide)

end SszArm.Codec.Measure
