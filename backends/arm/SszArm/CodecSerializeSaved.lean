import SszArm.CodecSerializeOwnership
import SszArm.SerializeFinishReturn

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value)
open Delimited (MemoryFrame)

/-- Saved caller registers are outside every callee-owned byte, including when
an exhausted arena has a zero-length free suffix at an arbitrary address. -/
theorem measure_outside_saved {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (address : BitVec 64)
    (lower : args.stack.toNat - 48 ≤ address.toNat) (upper : address.toNat < args.stack.toNat) :
    ∀ span ∈ Measure.envelope s args.measure desc,
      address.toNat < span.1 ∨ span.1 + span.2 ≤ address.toNat := by
  have minimum := requiredStack_min desc
  have enough := owned.stackLow
  have stackEnd : args.stack.toNat - requiredStack desc + requiredStack desc = args.stack.toNat :=
    Nat.sub_add_cancel enough
  have arenaSeparate := (owned.arenaOwned.resolve_left (by decide))
    (args.stack.toNat - requiredStack desc, requiredStack desc)
    (by simp [stackSpans, Stack.envelope])
  have planAddress := SszArm.Serialize.plan_toNat args (by omega)
  have stackAddress := SszArm.Serialize.bodySP_toNat args (by omega)
  intro span member
  rcases List.mem_append.mp member with localMember | allocation
  · rcases List.mem_append.mp localMember with stack | result
    · simp only [Measure.stackWrites, SszArm.Serialize.Args.measure, Stack.envelope,
        List.mem_singleton] at stack
      subst span
      right
      dsimp
      rw [stackAddress]
      have calleeLow := requiredStack_measure desc
      omega
    · simp only [SszArm.Serialize.Args.measure, List.mem_singleton] at result
      subst span
      right
      dsimp
      rw [planAddress]
      omega
  · change span ∈ ((args.arena.toNat + 16, 8) ::
      (if (freeSpan s args).2 = 0 then [] else [freeSpan s args])) at allocation
    have included : span = (args.arena.toNat + 16, 8) ∨ span = freeSpan s args := by
      by_cases empty : (freeSpan s args).2 = 0
      · exact Or.inl (by simpa [empty] using allocation)
      · simpa [empty] using allocation
    rcases included with rfl | rfl
    · dsimp at arenaSeparate ⊢
      omega
    · rcases owned.freeOwned with empty | freeSeparate
      · dsimp [freeSpan] at empty ⊢
        omega
      · have separated := freeSeparate
          (args.stack.toNat - requiredStack desc, requiredStack desc)
          (by simp [stackSpans, Stack.envelope])
        dsimp at separated ⊢
        omega

/-- Byte framing, rather than a disjointness fiction for zero-sized spans,
protects each word saved in the still-live parent activation. -/
theorem measure_saved_read {s before after : ArmState} {args : Args}
    {desc : Desc} {value : Value} (owned : Owned s args desc value)
    (frame : MemoryFrame (Measure.envelope s args.measure desc) before after)
    (displacement : Nat) (lower : 96 ≤ displacement) (upper : displacement + 8 ≤ 144) :
    read_mem_bytes 8 (args.bodySP + BitVec.ofNat 64 displacement) after =
      read_mem_bytes 8 (args.bodySP + BitVec.ofNat 64 displacement) before := by
  have minimum := requiredStack_min desc
  have enough := owned.stackLow
  have stackAddress := SszArm.Serialize.bodySP_toNat args (by omega)
  have stackHigh := args.stack.isLt
  apply BoolCodec.read_bytes_congr
  intro index within
  change after.mem _ = before.mem _
  apply frame
  apply measure_outside_saved owned
  · bv_omega
  · bv_omega

end SszArm.Codec.Serialize
