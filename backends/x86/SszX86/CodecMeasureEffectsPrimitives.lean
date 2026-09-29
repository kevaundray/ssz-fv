import SszX86.CodecMeasureEffectsGeometry
import SszX86.CodecMeasureFixedArithmeticGeometry
import SszX86.MeasureResources

namespace SszX86.CodecMeasure.Geometry
open SszNative
open SszNative.CodecMeasure

theorem primitive_within (shape : Serialize.Desc) (value : Codec.Value)
    (arena : Delimited.ArenaState) (bounded : arena.base + arena.capacity ≤ 2 ^ 64) :
    Within (arena.base + arena.used) (arena.base + arena.capacity)
      (primitive shape value arena).effects := by
  rintro a ⟨effect, member, writes⟩
  simp only [primitive, List.mem_singleton] at member
  subst effect
  obtain ⟨call, member, reservation, allocated, span⟩ := writes
  obtain ⟨lower, upper⟩ :=
    (Measure.measure_resources shape value.toPrimitive arena).allocations
      call member reservation allocated
  obtain ⟨start, finish⟩ := span_bounds reservation.pointer (8 * call.written.length) a
    (upper.trans bounded) span
  exact ⟨lower.trans start, finish.trans_le upper⟩

theorem add_within (left right : NatOperand) (arena : Delimited.ArenaState)
    (bounded : arena.base + arena.capacity ≤ 2 ^ 64) :
    Within (arena.base + arena.used) (arena.base + arena.capacity)
      (add left right arena).effects := by
  rintro a ⟨effect, member, writes⟩
  simp only [add, List.mem_singleton] at member
  subst effect
  obtain ⟨lower, upper, capacity⟩ := CodecMeasureFixed.add_writes_geometry
    left right arena.base arena.capacity arena.used bounded a writes
  exact ⟨lower, upper.trans_le (Nat.add_le_add_left capacity arena.base)⟩

theorem exactCount_within (low high : Nat) (expected : NatOperand) (actual used : Nat) :
    Within low high (exactCount expected actual used).effects := by
  rw [(exactCount_resources expected actual used).2]
  rintro a ⟨effect, member, _⟩
  cases member

theorem bounded_within (low high : Nat) (limit : Option NatOperand)
    (actual : NatOperand) (used : Nat) :
    Within low high (SszNative.CodecMeasure.bounded limit actual used).effects := by
  rw [(bounded_resources limit actual used).2]
  rintro a ⟨effect, member, _⟩
  cases member

theorem hostSize_within (low high : Nat) (size : NatOperand) (used : Nat) :
    Within low high (hostSize size used).effects := by
  rw [(hostSize_resources size used).2]
  rintro a ⟨effect, member, _⟩
  cases member

theorem compositeSize_within (low high : Nat) (size : NatOperand) (used : Nat) :
    Within low high (compositeSize size used).effects := by
  rw [(compositeSize_resources size used).2]
  rintro a ⟨effect, member, _⟩
  cases member

theorem reservePlans_within (count : Nat) (arena : Delimited.ArenaState) (low high : Nat) :
    Within low high (reservePlans count arena).effects := by
  unfold reservePlans
  split <;> rintro a ⟨effect, member, writes⟩ <;>
    simp only [List.mem_singleton] at member <;> subst effect <;> exact writes.elim

theorem reserved_slots (count : Nat) (arena : Delimited.ArenaState)
    (reservation : Arena.Reservation) (_bounded : arena.base + arena.capacity ≤ 2 ^ 64)
    (reserved : Arena.reserve arena.base arena.capacity arena.used (5 * count) = some reservation) :
    Slots (arena.base + arena.used) (arena.base + arena.capacity) (some reservation) 0 count := by
  intro actual allocated i lower upper
  have same : reservation = actual := Option.some.inj allocated
  subst actual
  have positive : 0 < 5 * count := by omega
  obtain ⟨checks, shape⟩ :=
    (Arena.reserve_eq_some_iff_checks arena.base arena.capacity arena.used
      (5 * count) positive reservation).1 reserved
  have start := Arena.used_le_start arena.base arena.used
  have fits := checks.2.2.2.2.2
  rw [shape]
  dsimp only
  simp only [Arena.finish] at fits
  constructor <;> omega

end SszX86.CodecMeasure.Geometry
