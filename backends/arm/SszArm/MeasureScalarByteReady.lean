import SszArm.MeasureScalarScanStart

namespace SszArm.Measure.Scalar.Bytes

open SszNative (NatOperand)

theorem cap_at {s : ArmState} {args : Args} {kind : Kind} {cap : NatOperand} {bytes : Ssz.Bytes}
    (owned : Owned s args (kind.desc cap) (.bytes bytes)) : cap.At (UintCodec.widthLoad s) :=
  owned.operand_at cap (by cases kind <;> simp [Kind.desc, Emit.descriptorOperands, Emit.valueOperands])

theorem cap_borrowed {s : ArmState} {args : Args} {kind : Kind} {cap : NatOperand} {bytes : Ssz.Bytes}
    (owned : Owned s args (kind.desc cap) (.bytes bytes)) :
    NatDivision.OperandOwned (bodyWrites args (outcome s args (kind.desc cap) (.bytes bytes))) cap := by
  have borrowed := owned.operandOwned cap
    (by cases kind <;> simp [Kind.desc, Emit.descriptorOperands, Emit.valueOperands])
  cases cap with
  | small word => trivial
  | large pointer words =>
    rcases borrowed with empty | separate
    · exact Or.inl empty
    · exact Or.inr (fun span member => separate span (bodyWrites_subset args _ span member))

theorem ready_body (kind : Kind) (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bytes : Ssz.Bytes)
    (owned : Owned s args (kind.desc cap) (.bytes bytes))
    (output : r (.GPR 19#5) s = args.result) (stack : r (.GPR 31#5) s = args.bodySP)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (ready : Ready kind s base cap bytes.size) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (kind.desc cap) (.bytes bytes) base := by
  have physical : bytes.size < 2^64 := owned.physical
  have measured : outcome s args (kind.desc cap) (.bytes bytes) =
      SszNative.Serialize.unchanged (arenaOf s args).used
        (if kind.accepts cap bytes.size then .ok (SszNative.Serialize.count bytes.size)
         else .error (kind.failure cap bytes.size)) :=
    measure_bytes kind cap bytes (arenaOf s args) physical
  have calls := byte_calls kind s args cap bytes physical
  have used := byte_used kind s args cap bytes physical
  rcases ready with ⟨actual, selected⟩
  by_cases accepted : kind.accepts cap bytes.size
  · rw [if_pos accepted] at selected
    have success : (outcome s args (kind.desc cap) (.bytes bytes)).result =
        .ok (.small (BitVec.ofNat 64 bytes.size)) := by
      simp [measured, accepted, SszNative.Serialize.unchanged, SszNative.Serialize.count]
    refine ⟨33, Result.successResult s base,
      Result.success_run s base code error aligned selected.1, ?_⟩
    exact Result.success_produced base owned output stack (.small (BitVec.ofNat 64 bytes.size))
      success calls used selected.2 actual (by trivial) (by trivial) error
  · rw [if_neg accepted] at selected
    have failure : (outcome s args (kind.desc cap) (.bytes bytes)).result =
        .error (kind.failure cap bytes.size) := by
      simp [measured, accepted, SszNative.Serialize.unchanged]
    have input := cap_at owned
    have borrowed := cap_borrowed owned
    cases kind with
    | vector =>
      refine ⟨38, Result.scopeResult s base,
        Result.scope_run s base code error aligned selected.1, ?_⟩
      exact Result.scope_produced base owned output stack cap (BitVec.ofNat 64 bytes.size)
        failure calls used selected.2.1 selected.2.2 actual input borrowed error
    | list =>
      refine ⟨39, Result.limitResult s base,
        Result.limit_run s base code error aligned selected.1, ?_⟩
      exact Result.limit_produced base owned output stack cap (BitVec.ofNat 64 bytes.size)
        failure calls used selected.2.1 selected.2.2 actual input borrowed error

end SszArm.Measure.Scalar.Bytes
