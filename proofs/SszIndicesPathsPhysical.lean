import SszIndicesPaths
import SszIndicesDescriptorRefinement
import SszIndicesPhysical
import SszIndicesArithmeticShiftPhysical

set_option autoImplicit false

namespace SszNative.Indices

def PathStep.Physical : PathStep → Prop
  | .position ordinal => Indices.Physical ordinal
  | _ => True

theorem operandSliceSized_physical (operand : NatOperand)
    (physical : Codec.operandSliceSized operand) : Physical operand := by
  cases operand with
  | small word => exact small_physical word
  | large pointer words => exact physical

theorem itemLength_physical (shape : Codec.Desc) (physical : shape.Physical) :
    Physical (itemLength shape) := by
  cases shape with
  | primitive shape =>
      cases shape with
      | uint width => exact operandSliceSized_physical width physical
      | _ => exact small_physical _
  | _ => exact small_physical _

/-- Successful dependent phases preserve a postcondition; failed phases never
require a condition on an unexecuted continuation. -/
theorem pathBind_post {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (middle : α → Prop) (post : β → Prop)
    (before : ∀ value, first.result = .ok value → middle value)
    (after : ∀ value cursor, middle value → ∀ result,
      (next value cursor).result = .ok result → post result)
    (result : β) (success : (bind first next).result = .ok result) : post result := by
  cases observed : first.result with
  | error reason => simp only [bind, observed] at success; cases success
  | ok value =>
      exact after value first.used (before value observed) result
        (by simpa only [bind, observed] using success)

private theorem pathDivide_success (used : Nat)
    (outcome : NatArithmetic.Outcome (NatOperand × BitVec 64))
    (result : NatOperand × BitVec 64)
    (success : (divide used outcome).result = .ok result) :
    outcome.result = .ok result := by
  cases observed : outcome.result with
  | error reason =>
      simp only [divide, observed, Except.mapError] at success
      cases success
  | ok value =>
      simp only [divide, observed, Except.mapError, Except.ok.injEq] at success
      exact congrArg Except.ok success

private def optionalPhysical : Option NatOperand → Prop
  | none => True
  | some operand => Physical operand

theorem activePosition_success_physical (active : List Bool) (ordinal : NatOperand)
    (base capacity used : Nat) (result : Option NatOperand)
    (success : (activePosition active ordinal base capacity used).result = .ok result) :
    ∀ value, result = some value → Physical value := by
  have all : optionalPhysical result := by
    unfold activePosition at success
    split at success
    · cases success
      trivial
    · split at success
      · cases success
        trivial
      · apply pathBind_post _ _ Physical optionalPhysical ?_ ?_ result success
        · intro value succeeded
          exact fromWide_physical _ _ _ _ value (arithmetic_success _ _ value succeeded)
        · intro value cursor physical output succeeded
          cases succeeded
          exact physical
  intro value same
  simpa only [same, optionalPhysical] using all

theorem layoutPosition_success_physical (active : List Bool) (ordinal : NatOperand)
    (base capacity used : Nat) (result : NatOperand)
    (success : (layoutPosition active ordinal base capacity used).result = .ok result) :
    Physical result := by
  apply pathBind_post _ _ (fun value => ∀ operand, value = some operand → Physical operand)
    Physical ?_ ?_ result success
  · exact activePosition_success_physical active ordinal base capacity used
  · intro value cursor physical output succeeded
    cases value with
    | none => cases succeeded
    | some operand =>
        have same : operand = output := Except.ok.inj succeeded
        exact same ▸ physical operand rfl

theorem chunkCount_success_physical (shape : Codec.Desc) (base capacity used : Nat)
    (physical : shape.Physical) (result : NatOperand)
    (success : (chunkCount shape base capacity used).result = .ok result) : Physical result := by
  cases shape with
  | primitive shape =>
      cases shape with
      | bool | uint _ => cases success; exact small_physical _
      | progressiveBitList _ => cases success
      | byteVector count | byteList count | bitVector count | bitList count =>
          exact ceilShift_success_physical _ _ _ _ _
            (operandSliceSized_physical count physical) result success
  | compatibleUnion variants => cases success; exact small_physical _
  | container fields =>
      exact fromWide_physical _ _ _ _ result (arithmetic_success _ _ result success)
  | progressiveList element limit => cases success
  | progressiveContainer active fields => cases success
  | vector element count | list element count =>
      have widthPhysical := itemLength_physical element physical.1
      have countPhysical := operandSliceSized_physical count physical.2
      simp only [chunkCount] at success
      split at success
      · exact ceilShift_success_physical _ _ _ _ _ countPhysical result success
      · apply pathBind_post _ _ Physical Physical ?_ ?_ result success
        · intro product multiplied
          exact mul_physical _ _ _ _ _ countPhysical widthPhysical product
            (arithmetic_success _ _ product multiplied)
        · intro product cursor productPhysical output shifted
          exact ceilShift_success_physical _ _ _ _ _ productPhysical output shifted

theorem unpackedPosition_success_physical (position width : NatOperand) (base capacity used : Nat)
    (positionPhysical : Physical position) (widthPhysical : Physical width) (result : ChunkPosition)
    (success : (unpackedPosition position width base capacity used).result = .ok result) :
    Physical result.chunk := by
  apply pathBind_post _ _ Physical (fun placed => Physical placed.chunk) ?_ ?_ result success
  · intro product multiplied
    exact mul_physical _ _ _ _ _ positionPhysical widthPhysical product
      (arithmetic_success _ _ product multiplied)
  · intro product cursor productPhysical output succeeded
    apply pathBind_post _ _ (fun divided : NatOperand × BitVec 64 => Physical divided.1)
      (fun placed => Physical placed.chunk) ?_ ?_ output succeeded
    · intro divided division
      exact divide_physical _ _ _ _ _ productPhysical divided
        (pathDivide_success cursor _ divided division)
    · intro divided cursor dividedPhysical placed succeeded
      apply pathBind_post _ _ (fun _ => True) (fun placed => Physical placed.chunk)
        (fun _ _ => True.intro) ?_ placed succeeded
      intro stop cursor _ placed succeeded
      cases succeeded
      exact dividedPhysical

private theorem shiftedPosition_physical (position : NatOperand) (shift base capacity used : Nat)
    (physical : Physical position) (start stop : NatOperand) (result : ChunkPosition)
    (success : (bind (arithmetic used (NatShift.shr position shift base capacity used))
      (fun chunk cursor => unchanged cursor (.ok ⟨chunk, start, stop⟩))).result = .ok result) :
    Physical result.chunk := by
  apply pathBind_post _ _ Physical (fun placed => Physical placed.chunk) ?_ ?_ result success
  · intro chunk shifted
    exact NatShift.shr_physical _ _ _ _ _ chunk physical (arithmetic_success _ _ chunk shifted)
  · intro chunk cursor physical placed succeeded
    cases succeeded
    exact physical

theorem sequencePosition_success_physical (shape : Codec.Desc) (position width : NatOperand)
    (base capacity used : Nat) (positionPhysical : Physical position)
    (widthPhysical : Physical width) (result : ChunkPosition)
    (success : (sequencePosition shape position width base capacity used).result = .ok result) :
    Physical result.chunk := by
  cases shape <;> try (rename_i primitive; cases primitive)
  all_goals simp only [sequencePosition] at success
  all_goals first
    | exact shiftedPosition_physical _ _ _ _ _ positionPhysical _ _ result success
    | (split at success
       · exact shiftedPosition_physical _ _ _ _ _ positionPhysical _ _ result success
       · exact unpackedPosition_success_physical _ _ _ _ _ positionPhysical widthPhysical result success)

private theorem sequenceCount_success_physical (shape : Codec.Desc)
    (ordinal width : NatOperand) (base capacity used : Nat)
    (ordinalPhysical : Physical ordinal) (widthPhysical : Physical width)
    (result : ChunkPosition)
    (success : (bind (unchanged used (positionCount shape)) fun count cursor =>
      if count.any (fun count => decide (Limbs.nativeCmp ordinal.words count.words ≠ .lt)) then
        unchanged cursor (.error (.noSuchPosition ordinal))
      else sequencePosition shape ordinal width base capacity cursor).result = .ok result) :
    Physical result.chunk := by
  apply pathBind_post _ _ (fun _ => True) (fun placed => Physical placed.chunk)
    (fun _ _ => True.intro) ?_ result success
  intro count cursor _ placed succeeded
  split at succeeded
  · cases succeeded
  · exact sequencePosition_success_physical shape ordinal width base capacity cursor
      ordinalPhysical widthPhysical placed succeeded

theorem chunkPosition_success_physical (shape : Codec.Desc) (step : PathStep)
    (base capacity used : Nat) (physical : shape.Physical) (stepPhysical : step.Physical)
    (result : ChunkPosition)
    (success : (chunkPosition shape step base capacity used).result = .ok result) :
    Physical result.chunk := by
  apply pathBind_post _ _ Codec.Desc.Physical (fun placed => Physical placed.chunk) ?_ ?_
    result success
  · intro element found
    exact elementType_physical shape step element physical found
  · intro element cursor elementPhysical placed succeeded
    have widthPhysical := itemLength_physical element elementPhysical
    cases step with
    | length | activeFields | selector => cases shape <;> cases succeeded
    | position ordinal =>
        have ordinalPhysical : Physical ordinal := stepPhysical
        cases shape with
        | container fields =>
            have same : (⟨ordinal, .small 0, itemLength element⟩ : ChunkPosition) = placed :=
              Except.ok.inj succeeded
            exact same ▸ ordinalPhysical
        | progressiveContainer active fields =>
            apply pathBind_post _ _ Physical (fun placed => Physical placed.chunk)
              (layoutPosition_success_physical active ordinal base capacity cursor)
              ?_ placed succeeded
            intro position cursor positionPhysical placed succeeded
            have same : (⟨position, .small 0, itemLength element⟩ : ChunkPosition) = placed :=
              Except.ok.inj succeeded
            exact same ▸ positionPhysical
        | primitive primitive =>
            exact sequenceCount_success_physical (.primitive primitive) ordinal (itemLength element)
              base capacity cursor ordinalPhysical widthPhysical placed succeeded
        | vector child count =>
            exact sequenceCount_success_physical (.vector child count) ordinal (itemLength element)
              base capacity cursor ordinalPhysical widthPhysical placed succeeded
        | list child count =>
            exact sequenceCount_success_physical (.list child count) ordinal (itemLength element)
              base capacity cursor ordinalPhysical widthPhysical placed succeeded
        | progressiveList child limit =>
            exact sequenceCount_success_physical (.progressiveList child limit) ordinal (itemLength element)
              base capacity cursor ordinalPhysical widthPhysical placed succeeded
        | compatibleUnion variants =>
            exact sequenceCount_success_physical (.compatibleUnion variants) ordinal (itemLength element)
              base capacity cursor ordinalPhysical widthPhysical placed succeeded

private def resolvedPhysical (resolved : NatOperand × Option Codec.Desc) : Prop :=
  Physical resolved.1 ∧ ∀ child, resolved.2 = some child → child.Physical

theorem resolvePosition_success_physical (shape : Codec.Desc) (ordinal : NatOperand)
    (base capacity used : Nat) (physical : shape.Physical) (_ : Physical ordinal)
    (result : NatOperand × Option Codec.Desc)
    (success : (resolvePosition shape ordinal base capacity used).result = .ok result) :
    Physical result.1 ∧ ∀ child, result.2 = some child → child.Physical := by
  have finish (index : NatOperand) (cursor : Nat) (indexPhysical : Physical index)
      (output : NatOperand × Option Codec.Desc)
      (succeeded : (unchanged cursor ((elementType shape (.position ordinal)).map
        (fun child => (index, some child)))).result = .ok output) : resolvedPhysical output := by
    cases found : elementType shape (.position ordinal) with
    | error reason =>
        simp only [unchanged, found, Except.map] at succeeded
        cases succeeded
    | ok child =>
        simp only [unchanged, found, Except.map, Except.ok.injEq] at succeeded
        subst output
        refine ⟨indexPhysical, ?_⟩
        intro other same
        cases same
        exact elementType_physical shape (.position ordinal) child physical found
  cases shape <;> try (rename_i primitive; cases primitive)
  all_goals simp only [resolvePosition] at success
  all_goals first
    | (split at success
       · cases success
       · rename_i child found
         cases success
         refine ⟨small_physical _, ?_⟩
         intro other same
         cases same
         exact unionOption_physical _ _ _ physical found)
    | (apply pathBind_post _ _ (fun _ => True) resolvedPhysical (fun _ _ => True.intro)
         ?_ result success
       intro placed cursor _ output succeeded
       first
         | (apply pathBind_post _ _ Physical resolvedPhysical ?_ ?_ output succeeded
            · exact progressiveChunkIndex_success_physical _ _ _ _
            · exact finish)
         | (apply pathBind_post _ _ (fun _ => True) resolvedPhysical (fun _ _ => True.intro)
              ?_ output succeeded
            intro count cursor _ output succeeded
            apply pathBind_post _ _ Physical resolvedPhysical ?_ ?_ output succeeded
            · exact rebase_success_physical _ _ _ _ _
            · exact finish))

theorem resolveStep_success_physical (shape : Codec.Desc) (step : PathStep)
    (base capacity used : Nat) (physical : shape.Physical) (stepPhysical : step.Physical)
    (result : NatOperand × Option Codec.Desc)
    (success : (resolveStep shape step base capacity used).result = .ok result) :
    Physical result.1 ∧ ∀ child, result.2 = some child → child.Physical := by
  cases shape <;> try (rename_i primitive; cases primitive)
  all_goals cases step
  all_goals simp only [resolveStep] at success
  all_goals first
    | (solve | cases success)
    | exact resolvePosition_success_physical _ _ _ _ _ physical stepPhysical result success
    | (split at success
       · cases success
         exact ⟨small_physical _, by intro child same; cases same⟩
       · cases success)

theorem generalizedIndex_success_physical (shape : Codec.Desc) (path : List PathStep)
    (base capacity used : Nat) (physical : shape.Physical)
    (pathPhysical : ∀ step ∈ path, step.Physical) (result : NatOperand)
    (success : (generalizedIndex shape path base capacity used).result = .ok result) :
    Physical result := by
  induction path generalizing shape used result with
  | nil => cases success; exact small_physical _
  | cons step rest ih =>
      apply pathBind_post _ _ resolvedPhysical Physical ?_ ?_ result success
      · exact resolveStep_success_physical shape step base capacity used physical
          (pathPhysical step (by simp))
      · intro resolved cursor resolvedPhysical output succeeded
        cases target : resolved.2 with
        | none =>
            have terminal :
                ((if rest.isEmpty = true then unchanged cursor (.ok resolved.1)
                  else unchanged cursor (.error .noPartsMixin)) : Outcome NatOperand).result =
                    .ok output := by
              simpa only [target] using succeeded
            by_cases empty : rest.isEmpty = true
            · simp only [empty, ↓reduceIte] at terminal
              have same : resolved.1 = output := Except.ok.inj terminal
              exact same ▸ resolvedPhysical.1
            · simp only [empty] at terminal
              cases terminal
        | some child =>
            rw [target] at succeeded
            apply pathBind_post _ _ Physical Physical ?_ ?_ output succeeded
            · intro inner recursed
              exact ih child cursor (resolvedPhysical.2 child target)
                (fun step member => pathPhysical step (List.mem_cons_of_mem _ member)) inner recursed
            · intro inner cursor innerPhysical result concatenated
              exact concat_success_physical _ _ _ _ _ resolvedPhysical.1 innerPhysical result concatenated

end SszNative.Indices
