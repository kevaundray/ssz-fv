import SszCodecMeasureResourcesCore

set_option autoImplicit false

namespace SszX86.CodecMeasure
open SszNative

private theorem bind_used_bound {α β : Type} (arena : Delimited.ArenaState)
    (first : Serialize.Outcome α) (next : α → Nat → Serialize.Outcome β)
    (initial : first.used ≤ arena.capacity)
    (later : ∀ value, first.result = .ok value → (next value first.used).used ≤ arena.capacity) :
    (Serialize.bind first next).used ≤ arena.capacity := by
  cases result : first.result with
  | error reason => simpa only [Serialize.bind, result] using initial
  | ok value => simpa only [Serialize.bind, result] using later value result

private theorem fromWide_used_bound (arena : Delimited.ArenaState) (wide : BitVec 128)
    (usedBound : arena.used ≤ arena.capacity) :
    (Serialize.fromWide arena wide).used ≤ arena.capacity := by
  by_cases small : wide.toNat < 2 ^ 64
  · simpa only [Serialize.fromWide, NatArithmetic.fromWide, small, ↓reduceIte,
      NatArithmetic.unchanged] using usedBound
  · cases reserved : Arena.reserve arena.base arena.capacity arena.used 2 with
    | none =>
      simpa only [Serialize.fromWide, NatArithmetic.fromWide, small, ↓reduceIte,
        reserved, NatArithmetic.unchanged] using usedBound
    | some reservation =>
      obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks
        arena.base arena.capacity arena.used 2 (by decide) reservation).1 reserved
      simp only [Serialize.fromWide, NatArithmetic.fromWide, small, ↓reduceIte,
        reserved, NatArithmetic.committed]
      rw [shape]
      exact checks.2.2.2.2.2

private theorem list_used_bound (limit : Option NatOperand) (bits : Serialize.Packed)
    (arena : Delimited.ArenaState) (usedBound : arena.used ≤ arena.capacity) :
    (Serialize.measureList limit bits arena).used ≤ arena.capacity := by
  unfold Serialize.measureList
  have counted := fromWide_used_bound arena bits.count usedBound
  apply bind_used_bound arena _ _ counted
  intro actual result
  have checked := (Serialize.bounded_resources limit actual
    (Serialize.fromWide arena bits.count).used).1
  apply bind_used_bound arena _ _ (by simpa only [checked] using counted)
  intro ignored accepted
  simpa only [checked] using fromWide_used_bound
    {arena with used := (Serialize.fromWide arena bits.count).used}
    (BitVec.ofNat 128 (bits.count.toNat / 8 + 1)) counted

/-- Even an empty/null arena and capacities above isize retain their original
cursor bound. This fact needs no successful outcome or stronger Arena.Valid. -/
theorem primitive_used_bound (shape : Serialize.Desc) (value : Serialize.Value)
    (arena : Delimited.ArenaState) (usedBound : arena.used ≤ arena.capacity) :
    (Serialize.measure shape value arena).used ≤ arena.capacity := by
  cases shape <;> cases value <;> simp only [Serialize.measure]
  all_goals try { exact usedBound }
  · split <;> exact usedBound
  · split <;> exact usedBound
  · rename_i cap bytes
    apply bind_used_bound arena _ _ (by
      rw [(Serialize.bounded_resources (some cap) (Serialize.count bytes.size) arena.used).1]
      exact usedBound)
    intro ignored checked
    change (Serialize.bounded (some cap) (Serialize.count bytes.size) arena.used).used ≤ arena.capacity
    rw [(Serialize.bounded_resources (some cap) (Serialize.count bytes.size) arena.used).1]
    exact usedBound
  · rename_i length bits
    split
    · exact usedBound
    · apply bind_used_bound arena _ _ (fromWide_used_bound arena bits.count usedBound)
      intro actual counted
      exact fromWide_used_bound arena bits.count usedBound
  · exact list_used_bound _ _ arena usedBound
  · exact list_used_bound _ _ arena usedBound

end SszX86.CodecMeasure
