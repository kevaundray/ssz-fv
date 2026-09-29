import SszIndicesPaths
import SszIndicesArithmeticOperationResources
import SszIndicesProgressiveResources
import SszHashLayoutArithmeticResources

set_option autoImplicit false

namespace SszNative.Indices

/-- Composing phases keeps the caller's arena valid, on errors as well as successes. -/
theorem pathBind_cursor_bounds {α β : Type} (first : Outcome α)
    (next : α → Nat → Outcome β) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used)
    (before : used ≤ first.used ∧ first.used ≤ capacity)
    (after : ∀ value cursor, Arena.Valid base capacity cursor →
      cursor ≤ (next value cursor).used ∧ (next value cursor).used ≤ capacity) :
    used ≤ (bind first next).used ∧ (bind first next).used ≤ capacity := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using before
  | ok value =>
      have nextValid : Arena.Valid base capacity first.used :=
        ⟨valid.1, valid.2.1, valid.2.2.1, before.2⟩
      have bounds := after value first.used nextValid
      simpa only [bind, result] using And.intro (Nat.le_trans before.1 bounds.1) bounds.2

private theorem unchanged_bounds {α : Type} (base capacity used : Nat)
    (result : Except Error α) (valid : Arena.Valid base capacity used) :
    used ≤ (unchanged used result).used ∧ (unchanged used result).used ≤ capacity :=
  ⟨Nat.le_refl _, valid.2.2.2⟩

private theorem wide_bounds (wide : BitVec 128) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (arithmetic used (NatArithmetic.fromWide base capacity used wide)).used ∧
      (arithmetic used (NatArithmetic.fromWide base capacity used wide)).used ≤ capacity := by
  have safe := HashLayout.fromWide_cursorSafe wide ⟨base, capacity, used⟩
  exact ⟨safe.1, (safe.2 valid).2.2.2⟩

private theorem mul_bounds (left right : NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (arithmetic used (NatMul.run left right base capacity used)).used ∧
      (arithmetic used (NatMul.run left right base capacity used)).used ≤ capacity := by
  have safe := HashLayout.mul_cursorSafe left right ⟨base, capacity, used⟩
  exact ⟨safe.1, (safe.2 valid).2.2.2⟩

private theorem add_bounds (left right : NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (arithmetic used (NatAdd.run left right base capacity used)).used ∧
      (arithmetic used (NatAdd.run left right base capacity used)).used ≤ capacity := by
  have safe := HashLayout.add_cursorSafe left right ⟨base, capacity, used⟩
  exact ⟨safe.1, (safe.2 valid).2.2.2⟩

private theorem divide_bounds (operand : NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (divide used (NatDivision.run operand 32 base capacity used)).used ∧
      (divide used (NatDivision.run operand 32 base capacity used)).used ≤ capacity := by
  have safe := HashLayout.divide_cursorSafe operand 32 ⟨base, capacity, used⟩
  exact ⟨safe.1, (safe.2 valid).2.2.2⟩

theorem activePosition_cursor_bounds (active : List Bool) (ordinal : NatOperand)
    (base capacity used : Nat) (valid : Arena.Valid base capacity used) :
    used ≤ (activePosition active ordinal base capacity used).used ∧
      (activePosition active ordinal base capacity used).used ≤ capacity := by
  unfold activePosition
  split
  · exact unchanged_bounds _ _ _ _ valid
  · split
    · exact unchanged_bounds _ _ _ _ valid
    · apply pathBind_cursor_bounds _ _ _ _ _ valid (wide_bounds _ _ _ _ valid)
      intro value cursor valid
      exact unchanged_bounds _ _ _ _ valid

theorem layoutPosition_cursor_bounds (active : List Bool) (ordinal : NatOperand)
    (base capacity used : Nat) (valid : Arena.Valid base capacity used) :
    used ≤ (layoutPosition active ordinal base capacity used).used ∧
      (layoutPosition active ordinal base capacity used).used ≤ capacity := by
  apply pathBind_cursor_bounds _ _ _ _ _ valid
    (activePosition_cursor_bounds active ordinal base capacity used valid)
  intro value cursor valid
  exact unchanged_bounds _ _ _ _ valid

theorem chunkCount_cursor_bounds (shape : Codec.Desc) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (chunkCount shape base capacity used).used ∧
      (chunkCount shape base capacity used).used ≤ capacity := by
  cases shape with
  | primitive shape =>
      cases shape <;> first
        | exact unchanged_bounds _ _ _ _ valid
        | exact ceilShift_cursor_bounds _ _ _ _ _ valid
  | compatibleUnion variants => exact unchanged_bounds _ _ _ _ valid
  | container fields => exact wide_bounds _ _ _ _ valid
  | progressiveContainer active fields => exact unchanged_bounds _ _ _ _ valid
  | progressiveList child limit => exact unchanged_bounds _ _ _ _ valid
  | vector element count | list element count =>
      simp only [chunkCount]
      split
      · exact ceilShift_cursor_bounds _ _ _ _ _ valid
      · apply pathBind_cursor_bounds _ _ _ _ _ valid (mul_bounds _ _ _ _ _ valid)
        intro product cursor valid
        exact ceilShift_cursor_bounds _ _ _ _ _ valid

theorem unpackedPosition_cursor_bounds (position width : NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (unpackedPosition position width base capacity used).used ∧
      (unpackedPosition position width base capacity used).used ≤ capacity := by
  apply pathBind_cursor_bounds _ _ _ _ _ valid (mul_bounds _ _ _ _ _ valid)
  intro product cursor valid
  apply pathBind_cursor_bounds _ _ _ _ _ valid (divide_bounds _ _ _ _ valid)
  intro divided cursor valid
  apply pathBind_cursor_bounds _ _ _ _ _ valid (add_bounds _ _ _ _ _ valid)
  intro stop cursor valid
  exact unchanged_bounds _ _ _ _ valid

private theorem shift_result_bounds {α : Type} (position : NatOperand) (shift : Nat)
    (f : NatOperand → α) (base capacity used : Nat) (valid : Arena.Valid base capacity used) :
    used ≤ (bind (arithmetic used (NatShift.shr position shift base capacity used))
      (fun result cursor => unchanged cursor (.ok (f result)))).used ∧
      (bind (arithmetic used (NatShift.shr position shift base capacity used))
        (fun result cursor => unchanged cursor (.ok (f result)))).used ≤ capacity := by
  apply pathBind_cursor_bounds _ _ _ _ _ valid
    (NatShift.shr_cursor_bounds _ _ _ _ _ valid)
  intro result cursor valid
  exact unchanged_bounds _ _ _ _ valid

theorem sequencePosition_cursor_bounds (shape : Codec.Desc) (position width : NatOperand)
    (base capacity used : Nat) (valid : Arena.Valid base capacity used) :
    used ≤ (sequencePosition shape position width base capacity used).used ∧
      (sequencePosition shape position width base capacity used).used ≤ capacity := by
  cases shape <;> try (rename_i primitive; cases primitive)
  all_goals simp only [sequencePosition]
  all_goals first
    | exact shift_result_bounds _ _ _ _ _ _ valid
    | (split
       · exact shift_result_bounds _ _ _ _ _ _ valid
       · exact unpackedPosition_cursor_bounds _ _ _ _ _ valid)

theorem chunkPosition_cursor_bounds (shape : Codec.Desc) (step : PathStep)
    (base capacity used : Nat) (valid : Arena.Valid base capacity used) :
    used ≤ (chunkPosition shape step base capacity used).used ∧
      (chunkPosition shape step base capacity used).used ≤ capacity := by
  apply pathBind_cursor_bounds _ _ _ _ _ valid (unchanged_bounds _ _ _ _ valid)
  intro element cursor valid
  cases shape <;> cases step
  all_goals simp only
  all_goals first
    | exact unchanged_bounds _ _ _ _ valid
    | (apply pathBind_cursor_bounds _ _ _ _ _ valid
         (layoutPosition_cursor_bounds _ _ _ _ _ valid)
       intro position cursor valid
       exact unchanged_bounds _ _ _ _ valid)
    | (apply pathBind_cursor_bounds _ _ _ _ _ valid (unchanged_bounds _ _ _ _ valid)
       intro count cursor valid
       split
       · exact unchanged_bounds _ _ _ _ valid
       · exact sequencePosition_cursor_bounds _ _ _ _ _ _ valid)

private theorem progressiveResolve_bounds (shape : Codec.Desc) (ordinal : NatOperand)
    (base capacity used : Nat) (valid : Arena.Valid base capacity used) :
    let outcome := bind (chunkPosition shape (.position ordinal) base capacity used)
      fun placed cursor =>
        bind (progressiveChunkIndex placed.chunk base capacity cursor) fun index cursor =>
          unchanged cursor ((elementType shape (.position ordinal)).map
            (fun child => (index, some child)))
    used ≤ outcome.used ∧ outcome.used ≤ capacity := by
  apply pathBind_cursor_bounds _ _ base capacity used valid
    (chunkPosition_cursor_bounds shape (.position ordinal) base capacity used valid)
  intro placed cursor valid
  apply pathBind_cursor_bounds _ _ base capacity cursor valid
    (progressiveChunkIndex_cursor_bounds placed.chunk base capacity cursor valid)
  intro index cursor valid
  exact unchanged_bounds base capacity cursor _ valid

private theorem boundedResolve_bounds (shape : Codec.Desc) (ordinal : NatOperand)
    (base capacity used : Nat) (valid : Arena.Valid base capacity used) :
    let outcome := bind (chunkPosition shape (.position ordinal) base capacity used)
      fun placed cursor =>
        bind (chunkCount shape base capacity cursor) fun count cursor =>
          bind (rebase placed.chunk
            (leafDepth count + if isBoundedList shape then 1 else 0) base capacity cursor)
            fun index cursor => unchanged cursor ((elementType shape (.position ordinal)).map
              (fun child => (index, some child)))
    used ≤ outcome.used ∧ outcome.used ≤ capacity := by
  apply pathBind_cursor_bounds _ _ base capacity used valid
    (chunkPosition_cursor_bounds shape (.position ordinal) base capacity used valid)
  intro placed cursor valid
  apply pathBind_cursor_bounds _ _ base capacity cursor valid
    (chunkCount_cursor_bounds shape base capacity cursor valid)
  intro count cursor valid
  apply pathBind_cursor_bounds _ _ base capacity cursor valid
    (rebase_cursor_bounds placed.chunk
      (leafDepth count + if isBoundedList shape then 1 else 0) base capacity cursor valid)
  intro index cursor valid
  exact unchanged_bounds base capacity cursor _ valid

theorem resolvePosition_cursor_bounds (shape : Codec.Desc) (ordinal : NatOperand)
    (base capacity used : Nat) (valid : Arena.Valid base capacity used) :
    used ≤ (resolvePosition shape ordinal base capacity used).used ∧
      (resolvePosition shape ordinal base capacity used).used ≤ capacity := by
  cases shape with
  | compatibleUnion variants => exact unchanged_bounds base capacity used _ valid
  | progressiveContainer active fields =>
      exact progressiveResolve_bounds (.progressiveContainer active fields) ordinal
        base capacity used valid
  | progressiveList element limit =>
      exact progressiveResolve_bounds (.progressiveList element limit) ordinal
        base capacity used valid
  | primitive primitive =>
      cases primitive with
      | progressiveBitList limit =>
          exact progressiveResolve_bounds (.primitive (.progressiveBitList limit)) ordinal
            base capacity used valid
      | bool =>
          exact boundedResolve_bounds (.primitive .bool) ordinal base capacity used valid
      | uint width =>
          exact boundedResolve_bounds (.primitive (.uint width)) ordinal base capacity used valid
      | byteVector count =>
          exact boundedResolve_bounds (.primitive (.byteVector count)) ordinal base capacity used valid
      | byteList count =>
          exact boundedResolve_bounds (.primitive (.byteList count)) ordinal base capacity used valid
      | bitVector count =>
          exact boundedResolve_bounds (.primitive (.bitVector count)) ordinal base capacity used valid
      | bitList count =>
          exact boundedResolve_bounds (.primitive (.bitList count)) ordinal base capacity used valid
  | vector element count =>
      exact boundedResolve_bounds (.vector element count) ordinal base capacity used valid
  | list element count =>
      exact boundedResolve_bounds (.list element count) ordinal base capacity used valid
  | container fields =>
      exact boundedResolve_bounds (.container fields) ordinal base capacity used valid

theorem resolveStep_cursor_bounds (shape : Codec.Desc) (step : PathStep)
    (base capacity used : Nat) (valid : Arena.Valid base capacity used) :
    used ≤ (resolveStep shape step base capacity used).used ∧
      (resolveStep shape step base capacity used).used ≤ capacity := by
  cases shape <;> try (rename_i primitive; cases primitive)
  all_goals cases step
  all_goals simp only [resolveStep]
  all_goals first
    | exact unchanged_bounds _ _ _ _ valid
    | exact resolvePosition_cursor_bounds _ _ _ _ _ valid
    | (split <;> exact unchanged_bounds _ _ _ _ valid)

/-- Valid arenas never retreat or exceed capacity, including after failures in
an inner path or a late concat. No physical or schema-validity premise is needed. -/
theorem generalizedIndex_cursor_bounds (shape : Codec.Desc) (path : List PathStep)
    (base capacity used : Nat) (valid : Arena.Valid base capacity used) :
    used ≤ (generalizedIndex shape path base capacity used).used ∧
      (generalizedIndex shape path base capacity used).used ≤ capacity := by
  induction path generalizing shape used with
  | nil => exact unchanged_bounds _ _ _ _ valid
  | cons step rest ih =>
      apply pathBind_cursor_bounds _ _ _ _ _ valid
        (resolveStep_cursor_bounds shape step base capacity used valid)
      intro resolved cursor valid
      cases target : resolved.2 with
      | none =>
          simp only
          split <;> exact unchanged_bounds _ _ _ _ valid
      | some child =>
          simp only
          apply pathBind_cursor_bounds _ _ _ _ _ valid (ih child cursor valid)
          intro inner cursor valid
          exact concat_cursor_bounds _ _ _ _ _ valid

end SszNative.Indices
