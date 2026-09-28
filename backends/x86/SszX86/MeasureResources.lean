import SszX86.MeasureCore

namespace SszX86.Measure
open SszNative SszNative.Serialize

/-- A consequence of the accepted measure trace: every actual payload is inside
the original free suffix, even when a later error retains an earlier allocation. -/
structure Resources {α : Type} (arena : Delimited.ArenaState) (outcome : Outcome α) : Prop where
  monotone : arena.used ≤ outcome.used
  allocations : ∀ call ∈ outcome.calls, ∀ r, call.allocation = some r →
    arena.base + arena.used ≤ r.pointer ∧
      r.pointer + 8 * call.written.length ≤ arena.base + arena.capacity

theorem resources_unchanged {α : Type} (arena : Delimited.ArenaState) (result : Except Error α) :
    Resources arena (unchanged arena.used result) := by
  refine ⟨Nat.le_refl _, ?_⟩
  intro call member
  cases member

theorem resources_bind {α β : Type} (arena : Delimited.ArenaState) (first : Outcome α)
    (next : α → Nat → Outcome β) (initial : Resources arena first)
    (later : ∀ value, first.result = .ok value →
      Resources {arena with used := first.used} (next value first.used)) :
    Resources arena (Serialize.bind first next) := by
  cases result : first.result with
  | error reason =>
    refine ⟨?_, ?_⟩
    · simpa only [Serialize.bind, result] using initial.monotone
    · intro call member reservation allocated
      apply initial.allocations call _ reservation allocated
      simpa only [Serialize.bind, result] using member
  | ok value =>
    have following := later value result
    refine ⟨?_, ?_⟩
    · simpa only [Serialize.bind, result] using Nat.le_trans initial.monotone following.monotone
    · intro call member reservation allocated
      simp only [Serialize.bind, result, List.mem_append] at member
      rcases member with before | after
      · exact initial.allocations call before reservation allocated
      · obtain ⟨low, high⟩ := following.allocations call after reservation allocated
        change arena.base + first.used ≤ reservation.pointer at low
        exact ⟨Nat.le_trans (Nat.add_le_add_left initial.monotone arena.base) low, high⟩

theorem resources_fromWide (arena : Delimited.ArenaState) (wide : BitVec 128) :
    Resources arena (fromWide arena wide) := by
  by_cases small : wide.toNat < 2^64
  · refine ⟨by simp [fromWide, NatArithmetic.fromWide, small, NatArithmetic.unchanged], ?_⟩
    intro call member reservation allocated
    simp only [fromWide, NatArithmetic.fromWide, small, ↓reduceIte, List.mem_singleton] at member
    subst call
    cases allocated
  · cases reserved : Arena.reserve arena.base arena.capacity arena.used 2 with
    | none =>
      refine ⟨by simp [fromWide, NatArithmetic.fromWide, small, reserved, NatArithmetic.unchanged], ?_⟩
      intro call member reservation allocated
      simp only [fromWide, NatArithmetic.fromWide, small, ↓reduceIte, reserved,
        List.mem_singleton] at member
      subst call
      cases allocated
    | some reservation =>
      obtain ⟨checks, shape⟩ :=
        (Arena.reserve_eq_some_iff_checks arena.base arena.capacity arena.used 2 (by decide) reservation).1 reserved
      have usedStart := Arena.used_le_start arena.base arena.used
      refine ⟨?_, ?_⟩
      · simp only [fromWide, NatArithmetic.fromWide, small, ↓reduceIte, reserved,
          NatArithmetic.committed]
        rw [shape]
        simp only [Arena.finish]
        omega
      · intro call member r allocated
        simp only [fromWide, NatArithmetic.fromWide, small, ↓reduceIte, reserved,
          List.mem_singleton] at member
        subst call
        simp only [NatArithmetic.committed, Option.some.injEq] at allocated
        subst r
        change arena.base + arena.used ≤ reservation.pointer ∧
          reservation.pointer + 8 * 2 ≤ arena.base + arena.capacity
        rw [shape]
        dsimp only
        constructor
        · omega
        · have fits := checks.2.2.2.2.2
          simp only [Arena.finish] at fits
          omega

theorem resources_bounded (arena : Delimited.ArenaState) (limit : Option NatOperand)
    (actual : NatOperand) : Resources arena (bounded limit actual arena.used) := by
  have fields := bounded_resources limit actual arena.used
  refine ⟨by rw [fields.1]; exact Nat.le_refl _, ?_⟩
  intro call member
  rw [fields.2] at member
  cases member

theorem resources_list (limit : Option NatOperand) (bits : Packed)
    (arena : Delimited.ArenaState) : Resources arena (measureList limit bits arena) := by
  unfold measureList
  apply resources_bind arena _ _ (resources_fromWide arena bits.count)
  intro actual counted
  apply resources_bind _ _ _ (resources_bounded _ limit actual)
  intro ignored checked
  have unchangedUsed := (bounded_resources limit actual (fromWide arena bits.count).used).1
  simpa only [unchangedUsed] using
    resources_fromWide {arena with used := (fromWide arena bits.count).used}
      (BitVec.ofNat 128 (bits.count.toNat / 8 + 1))

theorem measure_resources (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    Resources arena (measure desc value arena) := by
  cases desc <;> cases value <;> simp only [Serialize.measure]
  all_goals try { exact resources_unchanged arena _ }
  · split <;> exact resources_unchanged arena _
  · split <;> exact resources_unchanged arena _
  · rename_i cap bytes
    apply resources_bind arena _ _ (resources_bounded arena (some cap) (count bytes.size))
    intro ignored checked
    exact resources_unchanged _ _
  · rename_i length bits
    split
    · exact resources_unchanged arena _
    · apply resources_bind arena _ _ (resources_fromWide arena bits.count)
      intro actual counted
      exact resources_unchanged _ _
  · exact resources_list _ _ _
  · exact resources_list _ _ _

end SszX86.Measure
