import SszHashLayoutArithmetic

set_option autoImplicit false

namespace SszNative.HashLayout

/-- Semantic arithmetic has no rejection other than the actual resource error. -/
def OnlyExhaustion {α : Type} (outcome : Outcome α) : Prop :=
  ∀ reason, outcome.result = .error reason → reason = arithmeticError .scratchExhausted

theorem arithmetic_onlyExhaustion {α : Type}
    (result : Except NatArithmetic.Failure α)
    (allowed : result ≠ .error .badRepresentation) (used : Nat) (effects : List Effect) :
    OnlyExhaustion ⟨arithmeticResult result, used, effects⟩ := by
  intro reason failed
  obtain ⟨failure, raw, same⟩ := (arithmeticResult_error_iff result reason).mp failed
  cases failure with
  | scratchExhausted => exact same.symm
  | badRepresentation => exact False.elim (allowed raw)

theorem fromWide_onlyExhaustion (wide : BitVec 128) (arena : Delimited.ArenaState) :
    OnlyExhaustion (fromWide wide arena) := by
  apply arithmetic_onlyExhaustion
  unfold NatArithmetic.fromWide
  split
  · simp [NatArithmetic.unchanged]
  · split <;> simp [NatArithmetic.unchanged, NatArithmetic.committed]

theorem add_onlyExhaustion (left right : NatOperand) (arena : Delimited.ArenaState) :
    OnlyExhaustion (add left right arena) :=
  arithmetic_onlyExhaustion _ (NatAdd.no_badRepresentation _ _ _ _ _) _ _

theorem mul_onlyExhaustion (left right : NatOperand) (arena : Delimited.ArenaState) :
    OnlyExhaustion (mul left right arena) :=
  arithmetic_onlyExhaustion _ (NatMul.no_badRepresentation _ _ _ _ _) _ _

theorem divide_onlyExhaustion (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) (nonzero : divisor ≠ 0) :
    OnlyExhaustion (divide operand divisor arena) := by
  apply arithmetic_onlyExhaustion
  intro failed
  exact nonzero ((NatDivision.run_badRepresentation_iff _ _ _ _ _).mp failed)

theorem unchanged_onlyExhaustion {α : Type} (used : Nat) (value : α) :
    OnlyExhaustion (unchanged used (.ok value)) := by
  intro reason failed
  cases failed

theorem bind_onlyExhaustion {α β : Type} (first : Outcome α)
    (next : α → Nat → Outcome β) (allowedFirst : OnlyExhaustion first)
    (allowedNext : ∀ value used, OnlyExhaustion (next value used)) :
    OnlyExhaustion (bind first next) := by
  intro reason failed
  cases result : first.result with
  | error firstReason =>
    simp only [bind, result, Except.error.injEq] at failed
    subst firstReason
    exact allowedFirst reason result
  | ok value =>
    exact allowedNext value first.used reason (by simpa only [bind, result] using failed)

theorem ceilDiv_onlyExhaustion (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) (nonzero : divisor ≠ 0) :
    OnlyExhaustion (ceilDiv operand divisor arena) := by
  apply bind_onlyExhaustion _ _ (divide_onlyExhaustion operand divisor arena nonzero)
  intro pair used
  split
  · exact unchanged_onlyExhaustion _ _
  · exact add_onlyExhaustion _ _ _

/-- Unconditional completeness modulo the returned resource error: no future
success or sufficient-scratch premise is required. -/
theorem ceilDiv_correct (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) (nonzero : divisor ≠ 0) :
    (ceilDiv operand divisor arena).result = .error (arithmeticError .scratchExhausted) ∨
      ∃ result, (ceilDiv operand divisor arena).result = .ok result ∧
        result.value = (operand.value + divisor.toNat - 1) / divisor.toNat := by
  cases outcome : (ceilDiv operand divisor arena).result with
  | error reason =>
    have same := ceilDiv_onlyExhaustion operand divisor arena nonzero reason outcome
    exact Or.inl (congrArg Except.error same)
  | ok result => exact Or.inr ⟨result, rfl,
      ceilDiv_value operand divisor arena nonzero result outcome⟩

/-- Zero divisor wins before operand inspection or any allocator checks. -/
theorem ceilDiv_zero (operand : NatOperand) (arena : Delimited.ArenaState) :
    ceilDiv operand 0 arena =
      ⟨.error (arithmeticError .badRepresentation), arena.used,
        [.divide operand 0 arena
          (NatArithmetic.unchanged arena.used (.error .badRepresentation))]⟩ := by
  simp only [ceilDiv, divide, NatDivision.phase_zero, NatArithmetic.unchanged,
    arithmeticResult, bind]

/-- Division error retention also exposes the accepted raw helper outcome,
including the absence of writes on that failing attempt. -/
theorem divide_failure (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) (failure : NatArithmetic.Failure)
    (failed : (NatDivision.run operand divisor arena.base arena.capacity arena.used).result =
      .error failure) :
    divide operand divisor arena =
      ⟨.error (arithmeticError failure), arena.used,
        [.divide operand divisor arena (NatArithmetic.unchanged arena.used (.error failure))]⟩ := by
  rw [divide, NatDivision.failure_unchanged _ _ _ _ _ _ failed]
  rfl

theorem add_failure (left right : NatOperand) (arena : Delimited.ArenaState)
    (failure : NatArithmetic.Failure)
    (failed : (NatAdd.run left right arena.base arena.capacity arena.used).result = .error failure) :
    add left right arena =
      ⟨.error (arithmeticError failure), arena.used,
        [.add left right arena (NatArithmetic.unchanged arena.used (.error failure))]⟩ := by
  rw [add, NatAdd.failure_unchanged _ _ _ _ _ _ failed]
  rfl

theorem mul_failure (left right : NatOperand) (arena : Delimited.ArenaState)
    (failure : NatArithmetic.Failure)
    (failed : (NatMul.run left right arena.base arena.capacity arena.used).result = .error failure) :
    mul left right arena =
      ⟨.error (arithmeticError failure), arena.used,
        [.mul left right arena (NatArithmetic.unchanged arena.used (.error failure))]⟩ := by
  rw [mul, NatMul.failure_unchanged _ _ _ _ _ _ failed]
  rfl

/-- A second-stage failure retains the successful division and the failed ONE
addition. Its returned cursor is the division cursor, never the original one. -/
theorem ceilDiv_add_failure (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) (quotient : NatOperand) (remainder : BitVec 64)
    (divided : (divide operand divisor arena).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0) (failure : NatArithmetic.Failure)
    (failed : (NatAdd.run quotient (.small 1) arena.base arena.capacity
      (divide operand divisor arena).used).result = .error failure) :
    ceilDiv operand divisor arena =
      ⟨.error (arithmeticError failure), (divide operand divisor arena).used,
        (divide operand divisor arena).effects ++
          [.add quotient (.small 1) { arena with used := (divide operand divisor arena).used }
            (NatArithmetic.unchanged (divide operand divisor arena).used (.error failure))]⟩ := by
  rw [ceilDiv_increment operand divisor arena quotient remainder divided nonzero,
    add_failure quotient (.small 1) _ failure failed]

end SszNative.HashLayout
