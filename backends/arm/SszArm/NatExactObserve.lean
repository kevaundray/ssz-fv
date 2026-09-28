import SszArm.NatExactContract

namespace SszArm.NatExact

open UintCodec (widthLoad)
open Delimited (Protected)

/-- The successful private Result changes only the status word. Its entire
sixty-four-byte payload remains the caller's original bytes. -/
theorem Post.success_payload {s t : ArmState} {expected : SszNative.NatOperand}
    (owned : Owned s expected) (post : Post s t expected)
    (equal : expected.value = (r (.GPR 2#5) s).toNat) :
    widthLoad t (r (.GPR 0#5) s).toNat 64 = widthLoad s (r (.GPR 0#5) s).toNat 64 ∧
    ∀ a : BitVec 64, (r (.GPR 0#5) s).toNat ≤ a.toNat →
      a.toNat < (r (.GPR 0#5) s).toNat + 64 → t.mem a = s.mem a := by
  have accepted := (SszNative.NatNarrow.runExact_iff expected (r (.GPR 2#5) s)).2 equal
  have protectedPayload : Protected (writesFor s expected) (r (.GPR 0#5) s).toNat 64 := by
    right
    intro span member
    simp only [writesFor, accepted, ↓reduceIte, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl
    · left; omega
    · have payloadStack := owned.outputStack.subspan 0 64 (by decide)
      simp only [Nat.add_zero] at payloadStack
      rcases payloadStack with empty | separate
      · omega
      · exact separate _ (by simp)
  have bound := owned.outputBound
  refine ⟨post.frame.load _ _ (by omega) protectedPayload, ?_⟩
  intro a low high
  exact post.frame.protected_byte protectedPayload a low high

end SszArm.NatExact
