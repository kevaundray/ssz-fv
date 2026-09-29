import SszIndicesFrontierResourcesRuns

set_option autoImplicit false

namespace SszNative.Indices

theorem bind_used_mono {α β : Type} (used : Nat) (first : Outcome α)
    (next : α → Nat → Outcome β) (before : used ≤ first.used)
    (after : ∀ value cursor, cursor ≤ (next value cursor).used) :
    used ≤ (bind first next).used := by
  cases returned : first.result with
  | error reason => simpa only [bind, returned] using before
  | ok value => simpa only [bind, returned] using Nat.le_trans before (after value first.used)

theorem fillLevels_used_mono (reservation : Arena.Reservation) (keepCandidate : Nat → Bool)
    (make : Nat → Nat → Outcome NatOperand)
    (monotone : ∀ level cursor, cursor ≤ (make level cursor).used)
    (remaining level slot used : Nat) :
    used ≤ (fillLevels reservation keepCandidate make remaining level slot used).used := by
  induction remaining generalizing level slot used with
  | zero => exact Nat.le_refl _
  | succ remaining ih =>
    simp only [fillLevels]
    split
    · apply bind_used_mono used _ _ (monotone level used)
      intro value cursor
      apply bind_used_mono cursor _ _ (Nat.le_refl _)
      intro accepted cursor
      apply bind_used_mono cursor _ _ (ih (level + 1) (slot + 1) cursor)
      intro result cursor
      exact Nat.le_refl _
    · exact ih (level + 1) slot used

theorem fillClaims_used_mono (indices : List NatOperand) (helpers : Bool)
    (reservation : Arena.Reservation) (base capacity : Nat)
    (remaining : List NatOperand) (claim slot used : Nat) :
    used ≤ (fillClaims indices helpers reservation base capacity remaining claim slot used).used := by
  induction remaining generalizing claim slot used with
  | nil => exact Nat.le_refl _
  | cons index rest ih =>
    unfold fillClaims
    apply bind_used_mono used
    · apply fillLevels_used_mono
      intro level cursor
      cases helpers
      · exact NatShift.shr_cursor index level base capacity cursor
      · exact shiftXor_used_mono index level true base capacity cursor
    · intro first cursor
      apply bind_used_mono cursor _ _ (ih (claim + 1) first.2 cursor)
      intro second cursor
      exact Nat.le_refl _

private theorem bind_success_used {α β : Type} (value : α) (cursor : Nat)
    (effects : List Effect) (next : α → Nat → Outcome β) :
    (bind ⟨.ok value, cursor, effects⟩ next).used = (next value cursor).used := rfl

/-- Once the outer path array was reserved, even a later failed initializer
returns a cursor at or beyond that committed reservation. No valid-arena premise
is needed for this retention statement. -/
theorem pathIndices_retains_reservation (index : NatOperand) (base capacity used count : Nat)
    (reservation : Arena.Reservation) (measured : length index = .ok count)
    (small : count < 2^64)
    (reserved : TypedArena.reserve natLayout base capacity used count = some reservation) :
    reservation.used ≤ (pathIndices index base capacity used).used := by
  have notWide : ¬ count ≥ 2^64 := by omega
  have monotone := fillLevels_used_mono reservation (fun _ => true)
    (fun level cursor => arithmetic cursor (NatShift.shr index level base capacity cursor))
    (fun level cursor => NatShift.shr_cursor index level base capacity cursor)
    count 0 0 reservation.used
  have retained := bind_used_mono reservation.used
    (fillLevels reservation (fun _ => true)
      (fun level cursor => arithmetic cursor (NatShift.shr index level base capacity cursor))
      count 0 0 reservation.used)
    (fun result cursor => unchanged cursor (.ok (⟨result.1, reservation⟩ : NatSlice)))
    monotone (fun _ _ => Nat.le_refl _)
  simp only [pathIndices, measured, bind_unchanged, notWide, ↓reduceIte]
  simp only [reserveNats, reserved, bind_success_used]
  exact retained

theorem branchIndices_retains_reservation (index : NatOperand) (base capacity used count : Nat)
    (reservation : Arena.Reservation) (measured : length index = .ok count)
    (small : count < 2^64)
    (reserved : TypedArena.reserve natLayout base capacity used count = some reservation) :
    reservation.used ≤ (branchIndices index base capacity used).used := by
  have notWide : ¬ count ≥ 2^64 := by omega
  have monotone := fillLevels_used_mono reservation (fun _ => true)
    (fun level cursor => shiftXor index level true base capacity cursor)
    (fun level cursor => shiftXor_used_mono index level true base capacity cursor)
    count 0 0 reservation.used
  have retained := bind_used_mono reservation.used
    (fillLevels reservation (fun _ => true)
      (fun level cursor => shiftXor index level true base capacity cursor)
      count 0 0 reservation.used)
    (fun result cursor => unchanged cursor (.ok (⟨result.1, reservation⟩ : NatSlice)))
    monotone (fun _ _ => Nat.le_refl _)
  simp only [branchIndices, measured, bind_unchanged, notWide, ↓reduceIte]
  simp only [reserveNats, reserved, bind_success_used]
  exact retained

theorem collectPathIndices_retains_reservation (indices : List NatOperand)
    (base capacity used count : Nat) (reservation : Arena.Reservation)
    (counted : countPaths indices 0 = .ok count)
    (reserved : TypedArena.reserve natLayout base capacity used count = some reservation) :
    reservation.used ≤ (collectPathIndices indices base capacity used).used := by
  have retained := bind_used_mono reservation.used
    (fillClaims indices false reservation base capacity indices 0 0 reservation.used)
    (fun result cursor => unchanged cursor (.ok (⟨result.1, reservation⟩ : NatSlice)))
    (fillClaims_used_mono indices false reservation base capacity indices 0 0 reservation.used)
    (fun _ _ => Nat.le_refl _)
  simp only [collectPathIndices, counted, bind_unchanged]
  simp only [reserveNats, reserved, bind_success_used]
  exact retained

theorem helperIndices_retains_reservation (indices : List NatOperand)
    (base capacity used count : Nat) (reservation : Arena.Reservation)
    (validated : rejectRelated indices = .ok ())
    (counted : countHelpers indices indices 0 0 = .ok count)
    (reserved : TypedArena.reserve natLayout base capacity used count = some reservation) :
    reservation.used ≤ (helperIndices indices base capacity used).used := by
  have retained := bind_used_mono reservation.used
    (fillClaims indices true reservation base capacity indices 0 0 reservation.used)
    (fun result cursor =>
      let sorted := result.1.mergeSort (fun left right => right.value ≤ left.value)
      (⟨.ok ⟨sorted, reservation⟩, cursor, [.sorted reservation.pointer sorted]⟩ : Outcome NatSlice))
    (fillClaims_used_mono indices true reservation base capacity indices 0 0 reservation.used)
    (fun _ _ => Nat.le_refl _)
  simp only [helperIndices, validated, counted, bind_unchanged]
  simp only [reserveNats, reserved, bind_success_used]
  exact retained

end SszNative.Indices
