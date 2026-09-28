import SszArm.MeasureBitListSpaceNative

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)
open Delimited (Span Protected)

theorem width_space {schema : Schema} {s u : ArmState} {args : Args} {bits : Packed}
    {actual : NatOperand} (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ())
    (base : BitVec 64) : Constructor.Space (Width.result u base) := by
  have regs := width_registers pre base
  have low := owned.stackLow
  refine ⟨width_native_owned owned pre checked base, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [regs.2.2.2.1, regs.1]
  · rw [regs.2.2.2.2, regs.1]
  · rw [regs.1, Args.bodySP]
    bv_omega
  · exact Helpers.original_success_space owned (Width.result u base) regs.2.1 regs.1
  · rw [width_outcome owned pre base]
    cases second : (widthCall s args bits).result with
    | ok operand => trivial
    | error reason =>
      have scratchReason := Helpers.fromWide_failure_scratch (widthArena s args bits)
        (BitVec.ofNat 128 (bits.count.toNat / 8 + 1)) reason second
      have failure : (outcome s args schema.descriptor (.bits bits)).result =
          .error (.arithmetic .scratchExhausted) := by
        rw [width_model pre checked]
        simp only [second, scratchReason, Except.mapError]
      exact Helpers.original_copy_space owned (Width.result u base) regs.2.1 regs.1 failure
        (width_two_calls pre checked)
  · rw [regs.2.2.1]
    rcases owned.headerLocal with empty | separate
    · exact Or.inl empty
    · exact Or.inr (fun span member => separate span
        (width_tail_local_subset owned pre checked base span member))
  · rw [width_arena owned pre base]
    change Protected (Constructor.tailWrites (Width.result u base))
      ((arenaOf s args).base + (countCall s args bits).used)
      ((arenaOf s args).capacity - (countCall s args bits).used)
    have free := owned.free_after (countCall s args bits).used (count_used_monotone s args bits)
    rcases free with empty | separate
    · exact Or.inl empty
    · exact Or.inr (fun span member => separate span (List.mem_append.mpr (Or.inl
        (width_tail_local_subset owned pre checked base span member))))

end SszArm.Measure.Bits.List
