import SszArm.CodecSerializeEmitEntry

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value)
open Delimited (Protected)

 theorem emit_capacity (args : Args) (count : Nat) (fitting : count ≤ args.capacity.toNat) :
    (args.emit count).capacity.toNat = count := by
  have bound := args.capacity.isLt
  simp only [Args.emit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : count < 2^64)]

 theorem emit_stack_covered (args : Args) (desc : Desc) (count : Nat)
    (low : requiredStack desc ≤ args.stack.toNat) :
    BitVector.Covers (stackSpans args desc) (Emit.stackWrites (args.emit count) desc) := by
  have minimum := requiredStack_min desc
  change BitVector.Covers (Stack.envelope args.stack.toNat (requiredStack desc))
    (Stack.envelope args.bodySP.toNat (Emit.stackBytes desc))
  rw [SszArm.Serialize.bodySP_toNat args (by omega)]
  exact Stack.child_cover low (requiredStack_emit desc)

 theorem emit_writes_covered (args : Args) (desc : Desc) (count : Nat)
    (low : requiredStack desc ≤ args.stack.toNat) (fitting : count ≤ args.capacity.toNat) :
    BitVector.Covers (stackSpans args desc ++ externalSpans args)
      (Emit.writesFor (args.emit count) desc count) := by
  intro span member
  rcases List.mem_append.mp member with localMember | output
  · rcases List.mem_append.mp localMember with stack | result
    · obtain ⟨outer, included, lower, upper⟩ := emit_stack_covered args desc count low span stack
      exact ⟨outer, List.mem_append.mpr (Or.inl included), lower, upper⟩
    · simp only [Emit.resultWrites, Args.emit, List.mem_cons, List.mem_singleton] at result
      rcases result with rfl | rfl <;>
        refine ⟨(args.result.toNat, 72), by simp [externalSpans], ?_, ?_⟩ <;> dsimp <;> omega
  · by_cases empty : count = 0
    · simp [empty] at output
    · simp only [if_neg empty, Args.emit, List.mem_singleton] at output
      subst span
      have nonempty : args.capacity.toNat ≠ 0 := by omega
      exact ⟨(args.output.toNat, args.capacity.toNat), by simp [externalSpans, nonempty],
        Nat.le_refl _, by dsimp; omega⟩

 theorem emit_envelope_covered (s : ArmState) (args : Args) (desc : Desc) (count : Nat)
    (low : requiredStack desc ≤ args.stack.toNat) (fitting : count ≤ args.capacity.toNat) :
    BitVector.Covers (envelope s args desc) (Emit.writesFor (args.emit count) desc count) := by
  intro span member
  obtain ⟨outer, included, lower, upper⟩ := emit_writes_covered args desc count low fitting span member
  exact ⟨outer, List.mem_append.mpr (Or.inl included), lower, upper⟩

 theorem Owned.emit_result_stack {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (count : Nat) :
    Protected (Emit.stackWrites (args.emit count) desc) args.result.toNat 72 :=
  (emit_stack_covered args desc count owned.stackLow).protected owned.resultStack

 theorem Owned.emit_output_stack {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (count : Nat) (fitting : count ≤ args.capacity.toNat) :
    Protected (Emit.stackWrites (args.emit count) desc) args.output.toNat count := by
  have allOutput := (emit_stack_covered args desc count owned.stackLow).protected owned.outputStack
  simpa only [Nat.add_zero] using allOutput.subspan 0 count fitting

 theorem Owned.emit_output_result {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (count : Nat) (fitting : count ≤ args.capacity.toNat) :
    Protected (Emit.resultWrites (args.emit count)) args.output.toNat count := by
  have allOutput : Protected (Emit.resultWrites (args.emit count)) args.output.toNat args.capacity.toNat := by
    apply BitVector.Covers.protected (owned := owned.outputResult)
    intro span member
    simp only [Emit.resultWrites, Args.emit, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl <;>
      refine ⟨(args.result.toNat, 72), by simp, ?_, ?_⟩ <;> dsimp <;> omega
  simpa only [Nat.add_zero] using allOutput.subspan 0 count fitting

 theorem Owned.emit_free_protected {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (count : Nat) (fitting : count ≤ args.capacity.toNat) :
    Protected (Emit.writesFor (args.emit count) desc count) (freeSpan s args).1 (freeSpan s args).2 := by
  apply BitVector.Covers.protected (owned := owned.freeOwned)
  intro span member
  obtain ⟨outer, included, lower, upper⟩ :=
    emit_writes_covered args desc count owned.stackLow fitting span member
  exact ⟨outer, List.mem_append.mpr (Or.inl included), lower, upper⟩

end SszArm.Codec.Serialize
