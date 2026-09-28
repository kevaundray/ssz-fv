import SszFixedSize

namespace SszNative.FixedSize

open Serialize (Outcome unchanged)

/-- On a first-stage error, neither the committed cursor nor any call is lost. -/
theorem bind_error {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (reason : Serialize.Error) (failed : first.result = .error reason) :
    Serialize.bind first next = ⟨.error reason, first.used, first.calls⟩ := by
  simp only [Serialize.bind, failed]

/-- The continuation receives the committed cursor. Its calls follow every
first-stage call, even when the continuation fails or returns None. -/
theorem bind_success {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (value : α) (success : first.result = .ok value) :
    Serialize.bind first next =
      ⟨(next value first.used).result, (next value first.used).used,
        first.calls ++ (next value first.used).calls⟩ := by
  simp only [Serialize.bind, success]

theorem bind_second_error {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (value : α) (reason : Serialize.Error) (success : first.result = .ok value)
    (failed : (next value first.used).result = .error reason) :
    Serialize.bind first next = ⟨.error reason, (next value first.used).used,
      first.calls ++ (next value first.used).calls⟩ := by
  rw [bind_success first next value success, failed]

theorem bind_used_mono {α β : Type} (used : Nat) (first : Outcome α)
    (next : α → Nat → Outcome β) (firstMono : used ≤ first.used)
    (nextMono : ∀ value cursor, cursor ≤ (next value cursor).used) :
    used ≤ (Serialize.bind first next).used := by
  cases result : first.result with
  | error reason => simpa only [Serialize.bind, result] using firstMono
  | ok value =>
    simpa only [Serialize.bind, result] using Nat.le_trans firstMono (nextMono value first.used)

private theorem used_le_finish (base used words : Nat) : used ≤ Arena.finish base used words := by
  have start := Arena.used_le_start base used
  unfold Arena.finish
  omega

/-- Cursor monotonicity is derived from the checked addition's exact allocation
geometry, not from an assumed success or an artificial arena-validity premise. -/
theorem add_used_mono (left right : NatOperand) (arena : Delimited.ArenaState) :
    arena.used ≤ (add left right arena).used := by
  change arena.used ≤ (NatAdd.run left right arena.base arena.capacity arena.used).used
  cases allocated : (NatAdd.run left right arena.base arena.capacity arena.used).allocation with
  | none =>
    rw [(NatAdd.no_allocation_resources left right arena.base arena.capacity arena.used allocated).1]
    exact Nat.le_refl _
  | some reservation =>
    have geometry := NatAdd.allocation_geometry left right arena.base arena.capacity arena.used
      reservation allocated
    rw [geometry.2.2.1]
    exact used_le_finish _ _ _

theorem mul_used_mono (left right : NatOperand) (arena : Delimited.ArenaState) :
    arena.used ≤ (mul left right arena).used := by
  change arena.used ≤ (NatMul.run left right arena.base arena.capacity arena.used).used
  rcases NatMul.run_resources left right arena.base arena.capacity arena.used with
    ⟨result, same, _⟩ | ⟨reservation, words, positive, reserved, same⟩
  · rw [same]
    exact Nat.le_refl _
  · obtain ⟨_, shape⟩ := (Arena.reserve_eq_some_iff_checks arena.base arena.capacity
      arena.used words.length positive reservation).1 reserved
    rw [same, shape]
    exact used_le_finish _ _ _

theorem div8_used_mono (length : NatOperand) (arena : Delimited.ArenaState) :
    arena.used ≤ (div8 length arena).used := by
  change arena.used ≤ (NatDivision.run length 8 arena.base arena.capacity arena.used).used
  cases allocated : (NatDivision.run length 8 arena.base arena.capacity arena.used).allocation with
  | none =>
    rw [(NatDivision.no_allocation_resources length 8 arena.base arena.capacity arena.used allocated).1]
    exact Nat.le_refl _
  | some reservation =>
    obtain ⟨cursor, _, _, _, finish, _⟩ := NatDivision.allocation_resources length 8
      arena.base arena.capacity arena.used reservation allocated
    rw [cursor, finish]
    exact used_le_finish _ _ _

theorem bitWidth_used_mono (length : NatOperand) (arena : Delimited.ArenaState) :
    arena.used ≤ (bitWidth length arena).used := by
  unfold bitWidth
  apply bind_used_mono _ _ _ (div8_used_mono length arena)
  intro divided used
  split
  · exact Nat.le_refl _
  · exact add_used_mono divided.1 (.small 1) { arena with used := used }

theorem measurePrimitive_used_mono (shape : Serialize.Desc) (arena : Delimited.ArenaState) :
    arena.used ≤ (measurePrimitive shape arena).used := by
  cases shape with
  | bitVector length =>
    unfold measurePrimitive
    apply bind_used_mono _ _ _ (bitWidth_used_mono length arena)
    intro width used
    exact Nat.le_refl _
  | _ => exact Nat.le_refl _

mutual
  theorem measureFixed_used_mono (desc : Codec.Desc) (arena : Delimited.ArenaState) :
      arena.used ≤ (measureFixed desc arena).used := by
    cases desc with
    | primitive shape => exact measurePrimitive_used_mono shape arena
    | vector element length =>
      simp only [measureFixed]
      apply bind_used_mono _ _ _ (measureFixed_used_mono element arena)
      intro measured used
      cases measured with
      | none => exact Nat.le_refl _
      | some width =>
        apply bind_used_mono _ _ _ (mul_used_mono width length { arena with used := used })
        intro total used
        exact Nat.le_refl _
    | container fields => exact measureFields_used_mono fields (.small 0) arena
    | progressiveContainer active fields => exact measureFields_used_mono fields (.small 0) arena
    | _ => exact Nat.le_refl _

  theorem measureFields_used_mono (fields : List (String × Codec.Desc)) (total : NatOperand)
      (arena : Delimited.ArenaState) : arena.used ≤ (measureFields fields total arena).used := by
    cases fields with
    | nil => exact Nat.le_refl _
    | cons field rest =>
      rcases field with ⟨name, shape⟩
      simp only [measureFields]
      apply bind_used_mono _ _ _ (measureFixed_used_mono shape arena)
      intro measured used
      cases measured with
      | none => exact Nat.le_refl _
      | some width =>
        apply bind_used_mono _ _ _ (add_used_mono total width { arena with used := used })
        intro next used
        exact measureFields_used_mono rest next { arena with used := used }
end

/-- Includes errors and raw invalid schemas. Earlier successful allocations are
never rolled back by a later error; the public variable case stays unchanged. -/
theorem fixedSize_used_mono (desc : Codec.Desc) (arena : Delimited.ArenaState) :
    arena.used ≤ (fixedSize desc arena).used := by
  unfold fixedSize
  split
  · exact measureFixed_used_mono desc arena
  · exact Nat.le_refl _

end SszNative.FixedSize
