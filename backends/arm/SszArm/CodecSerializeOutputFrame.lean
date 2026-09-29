import SszArm.CodecSerializeOwnership

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value)
open Delimited (Span MemoryFrame)

/-- Before emission, only caller stack, native result storage, arena cursor and
free scratch can be modified. This excludes the caller's output slice. -/
def noOutputEnvelope (s : ArmState) (args : Args) (desc : Desc) : List Span :=
  stackSpans args desc ++ [(args.result.toNat, 72)] ++
    ((args.arena.toNat + 16, 8) :: (if (freeSpan s args).2 = 0 then [] else [freeSpan s args]))

 theorem noOutput_outside {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (address : BitVec 64)
    (lower : args.output.toNat ≤ address.toNat)
    (upper : address.toNat < args.output.toNat + args.capacity.toNat) :
    ∀ span ∈ noOutputEnvelope s args desc,
      address.toNat < span.1 ∨ span.1 + span.2 ≤ address.toNat := by
  have nonempty : args.capacity.toNat ≠ 0 := by omega
  have stackSeparate := owned.outputStack.resolve_left nonempty
  have resultSeparate := (owned.outputResult.resolve_left nonempty)
    (args.result.toNat, 72) (by simp)
  have arenaSeparate := (owned.arenaOwned.resolve_left (by decide))
    (args.output.toNat, args.capacity.toNat) (by simp [externalSpans, nonempty])
  intro span member
  rcases List.mem_append.mp member with localMember | allocation
  · rcases List.mem_append.mp localMember with stack | result
    · have apart := stackSeparate span stack
      omega
    · simp only [List.mem_singleton] at result
      subst span
      dsimp at resultSeparate ⊢
      omega
  · have included : span = (args.arena.toNat + 16, 8) ∨ span = freeSpan s args := by
      by_cases empty : (freeSpan s args).2 = 0
      · exact Or.inl (by simpa [empty] using allocation)
      · simpa [empty] using allocation
    rcases included with rfl | rfl
    · dsimp at arenaSeparate ⊢
      omega
    · rcases owned.freeOwned with empty | freeSeparate
      · dsimp [freeSpan] at empty ⊢
        omega
      · have apart := freeSeparate (args.output.toNat, args.capacity.toNat)
          (by simp [externalSpans, nonempty])
        dsimp at apart ⊢
        omega

 theorem noOutput_preserved {s before after : ArmState} {args : Args}
    {desc : Desc} {value : Value} (owned : Owned s args desc value)
    (frame : MemoryFrame (noOutputEnvelope s args desc) before after)
    (index : Nat) (inside : index < args.capacity.toNat) :
    after.mem (args.output + BitVec.ofNat 64 index) =
      before.mem (args.output + BitVec.ofNat 64 index) := by
  have bound := owned.output.2.2.1
  apply frame
  apply noOutput_outside owned
  · bv_omega
  · bv_omega

 theorem measure_noOutput_covered (s : ArmState) (args : Args) (desc : Desc)
    (low : requiredStack desc ≤ args.stack.toNat) :
    BitVector.Covers (noOutputEnvelope s args desc) (Measure.envelope s args.measure desc) := by
  intro span member
  rcases List.mem_append.mp member with localMember | allocation
  · obtain ⟨outer, included, lower, upper⟩ := measure_local_covered args desc low span localMember
    exact ⟨outer, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl included))),
      lower, upper⟩
  · change span ∈ ((args.arena.toNat + 16, 8) ::
      (if (freeSpan s args).2 = 0 then [] else [freeSpan s args])) at allocation
    exact ⟨span, List.mem_append.mpr (Or.inr allocation), Nat.le_refl _, Nat.le_refl _⟩

 theorem saved_noOutput_covered (s : ArmState) (args : Args) (desc : Desc)
    (low : requiredStack desc ≤ args.stack.toNat) :
    BitVector.Covers (noOutputEnvelope s args desc) (SszArm.Serialize.saveWrites args) := by
  intro span member
  obtain ⟨outer, included, lower, upper⟩ := save_covered args desc low span member
  exact ⟨outer, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl included))),
    lower, upper⟩

end SszArm.Codec.Serialize
