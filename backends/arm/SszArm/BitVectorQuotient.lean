import SszArm.BitVectorMemory

namespace SszArm.BitVector

/-- The constant divisor eight never takes the divisor-one borrowed-operand
shortcut. A Large quotient therefore refers to exactly the recorded new buffer;
normalization does not discard the remainder of that buffer's written span. -/
theorem quotient_origin (length quotient : SszNative.NatOperand) (remainder : BitVec 64)
    (base capacity used : Nat)
    (success : (SszNative.NatDivision.run length 8 base capacity used).result =
      .ok (quotient, remainder)) :
    (∃ value, quotient = .small value) ∨
      ∃ reservation, (SszNative.NatDivision.run length 8 base capacity used).allocation =
          some reservation ∧
        quotient = SszNative.NatOperand.fromWords (BitVec.ofNat 64 reservation.pointer)
          (SszNative.NatDivision.run length 8 base capacity used).written := by
  by_cases count : length.wordCount ≤ 2
  · have phase := SszNative.NatDivision.phase_wide length 8 base capacity used
      (by decide) (by decide) count
    rw [phase] at success ⊢
    by_cases small : (SszNative.NatDivision.wideQuotient length 8).toNat < 2^64
    · simp only [SszNative.NatArithmetic.fromWide, small, ↓reduceIte,
        SszNative.NatArithmetic.unchanged, Except.map, Except.ok.injEq, Prod.mk.injEq] at success
      exact Or.inl ⟨_, success.1.symm⟩
    · cases reserved : SszNative.Arena.reserve base capacity used 2 with
      | none =>
        simp only [SszNative.NatArithmetic.fromWide, small, ↓reduceIte, reserved,
          SszNative.NatArithmetic.unchanged, Except.map] at success
        cases success
      | some reservation =>
        simp only [SszNative.NatArithmetic.fromWide, small, ↓reduceIte, reserved,
          SszNative.NatArithmetic.committed, Except.map, Except.ok.injEq, Prod.mk.injEq] at success ⊢
        exact Or.inr ⟨reservation, rfl, success.1.symm⟩
  · have long : 2 < length.wordCount := by omega
    cases reserved : SszNative.Arena.reserve base capacity used length.wordCount with
    | none =>
      rw [SszNative.NatDivision.phase_reserve_failure length 8 base capacity used
        (by decide) (by decide) long reserved] at success
      cases success
    | some reservation =>
      have phase := SszNative.NatDivision.phase_reserved length 8 base capacity used
        (by decide) (by decide) long reservation reserved
      rw [phase] at success ⊢
      simp only [Except.ok.injEq, Prod.mk.injEq] at success
      exact Or.inr ⟨reservation, rfl, success.1.symm⟩

end SszArm.BitVector
