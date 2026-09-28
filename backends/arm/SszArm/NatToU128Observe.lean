import SszArm.NatToU128Contract

namespace SszArm.NatToU128

open UintCodec (widthLoad)
open Delimited (Protected)

/-- An unrepresentable input defines both tag words, without changing even one
byte of the sixteen-byte payload. This includes arbitrary prior payload data. -/
theorem Post.none_payload {s t : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned s operand) (post : Post s t operand)
    (large : 2^128 ≤ operand.value) :
    widthLoad t ((r (.GPR 0#5) s).toNat + 16) 16 =
      widthLoad s ((r (.GPR 0#5) s).toNat + 16) 16 ∧
    ∀ a : BitVec 64, (r (.GPR 0#5) s).toNat + 16 ≤ a.toNat →
      a.toNat < (r (.GPR 0#5) s).toNat + 32 → t.mem a = s.mem a := by
  have absent := (SszNative.NatNarrow.toU128_none_iff operand).2 large
  have protectedPayload : Protected (writesFor s operand)
      ((r (.GPR 0#5) s).toNat + 16) 16 := by
    right
    intro span member
    simp only [writesFor, absent, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · right; omega
    · have payloadStack := owned.outputStack.subspan 16 16 (by decide)
      rcases payloadStack with empty | separate
      · omega
      · exact separate _ (by simp)
  have bound := owned.outputBound
  refine ⟨post.frame.load _ _ (by omega) protectedPayload, ?_⟩
  intro a low high
  exact post.frame.protected_byte protectedPayload a low (by omega)

end SszArm.NatToU128
