import SszX86.CodecMeasureFixedArithmeticResources

namespace SszX86.CodecMeasureFixed
open SszNative

/-- Division by eight never borrows its input: every Large quotient comes from
this call's complete initialized allocation, before result normalization. -/
theorem divide8_result_provenance (operand : NatOperand) (base capacity used : Nat)
    (result : NatOperand × BitVec 64)
    (success : (SszNative.NatDivision.run operand 8 base capacity used).result = .ok result)
    (a : BitVec 64) (borrowed : Emit.NatBorrowed result.1 a) :
    ArithmeticWrites (SszNative.NatDivision.run operand 8 base capacity used) a := by
  by_cases small : operand.wordCount ≤ 2
  · rw [SszNative.NatDivision.phase_wide operand 8 base capacity used (by decide) (by decide) small]
    rw [SszNative.NatDivision.phase_wide operand 8 base capacity used (by decide) (by decide) small]
      at success
    cases outcome : (NatArithmetic.fromWide base capacity used
        (SszNative.NatDivision.wideQuotient operand 8)).result with
    | error error => simp only [outcome, Except.map] at success; cases success
    | ok quotient =>
      simp only [outcome, Except.map, Except.ok.injEq] at success
      subst result
      have provenance := fromWide_provenance (fun _ => False) base capacity used
        (SszNative.NatDivision.wideQuotient operand 8) quotient outcome a borrowed
      exact provenance.resolve_left (fun h => h)
  · cases reserved : Arena.reserve base capacity used operand.wordCount with
    | none =>
      rw [SszNative.NatDivision.phase_reserve_failure operand 8 base capacity used
        (by decide) (by decide) (by omega) reserved] at success
      cases success
    | some reservation =>
      rw [SszNative.NatDivision.phase_reserved operand 8 base capacity used
        (by decide) (by decide) (by omega) reservation reserved] at success ⊢
      cases success
      exact ⟨reservation, rfl, fromWords_borrowed _ _ a borrowed⟩

end SszX86.CodecMeasureFixed
