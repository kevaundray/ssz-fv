import SszX86.CodecMeasureCore
import SszCodecMeasureResourcesCore

namespace SszX86.CodecMeasure.Geometry
open SszNative
open SszNative.CodecMeasure

/-- Bounds constrain initialized bytes, not the merely reserved suffix. -/
def Within (low high : Nat) (effects : List Effect) : Prop :=
  ∀ a, EffectsWrite effects a → low ≤ a.toNat ∧ a.toNat < high

/-- An empty retained array imposes no condition on its dangling pointer. -/
def Slots (low high : Nat) (allocation : Option Arena.Reservation) (index count : Nat) : Prop :=
  ∀ reservation, allocation = some reservation → ∀ i, index ≤ i → i < index + count →
    low ≤ reservation.pointer + 40 * i ∧ reservation.pointer + 40 * i + 40 ≤ high

theorem Within.weaken {low high lo hi : Nat} {effects : List Effect}
    (h : Within low high effects) (lower : lo ≤ low) (upper : high ≤ hi) :
    Within lo hi effects := by
  intro a writes
  obtain ⟨left, right⟩ := h a writes
  exact ⟨lower.trans left, right.trans_le upper⟩

theorem Within.append {low high : Nat} {before after : List Effect}
    (first : Within low high before) (second : Within low high after) :
    Within low high (before ++ after) := by
  intro a writes
  rcases (EffectsWrite.append before after a).1 writes with old | new
  · exact first a old
  · exact second a new

theorem unchanged_within {α : Type} (low high used : Nat) (result : Except Codec.Error α) :
    Within low high (unchanged used result).effects := by
  rintro a ⟨effect, member, _⟩
  cases member

theorem bind_within {α β : Type} (low high : Nat) (first : Outcome α)
    (next : α → Nat → Outcome β) (before : Within low high first.effects)
    (after : ∀ value, first.result = .ok value → Within low high (next value first.used).effects) :
    Within low high (bind first next).effects := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using before
  | ok value =>
    simpa only [bind, result] using before.append (after value result)

theorem span_bounds (pointer count : Nat) (a : BitVec 64)
    (bounded : pointer + count ≤ 2 ^ 64)
    (span : Codec.InSpan a (BitVec.ofNat 64 pointer) count) :
    pointer ≤ a.toNat ∧ a.toNat < pointer + count := by
  obtain ⟨i, index, address⟩ := span
  have noWrap : pointer + i < 2 ^ 64 := by omega
  have exactAddress : a.toNat = pointer + i := by
    rw [address, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt noWrap]
  rw [exactAddress]
  omega

theorem Slots.tail {low high index count : Nat} {allocation : Option Arena.Reservation}
    (h : Slots low high allocation index (count + 1)) :
    Slots low high allocation (index + 1) count := by
  intro reservation allocated i lower upper
  exact h reservation allocated i (by omega) (by omega)

theorem writePlan_within (low high index used : Nat) (allocation : Option Arena.Reservation)
    (plan : Plan) (upper : high ≤ 2 ^ 64) (slots : Slots low high allocation index 1) :
    Within low high (writePlan allocation index plan used).effects := by
  cases allocation with
  | none => exact unchanged_within low high used (.ok ())
  | some reservation =>
    intro a writes
    obtain ⟨effect, member, written⟩ := writes
    simp only [writePlan, List.mem_singleton] at member
    subst effect
    obtain ⟨lower, endBound⟩ := slots reservation rfl index (Nat.le_refl _) (by omega)
    obtain ⟨start, finish⟩ := span_bounds (reservation.pointer + 40 * index) 40 a
      (endBound.trans upper) written
    exact ⟨lower.trans start, finish.trans_le endBound⟩

end SszX86.CodecMeasure.Geometry
