import SszX86.MeasureBitsResources
import SszX86.MeasureBitsArithmetic

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize

def countCall (bits : Packed) (address capacity used : BitVec 64) : NatArithmetic.Outcome NatOperand :=
  NatArithmetic.fromWide address.toNat capacity.toNat used.toNat bits.count

def encodedCall (bits : Packed) (address capacity used : BitVec 64) : NatArithmetic.Outcome NatOperand :=
  NatArithmetic.fromWide address.toNat capacity.toNat (countCall bits address capacity used).used
    (encodedWide bits.count)

theorem list_first_failure (limit : Option NatOperand) (bits : Packed)
    (address capacity used : BitVec 64) (reason : NatArithmetic.Failure)
    (failed : (countCall bits address capacity used).result = .error reason) :
    measureList limit bits (arenaState address capacity used) =
      ⟨.error (.arithmetic reason), (countCall bits address capacity used).used,
        [countCall bits address capacity used]⟩ := by
  simp only [measureList, fromWide, arenaState, SszNative.Serialize.bind, countCall] at failed ⊢
  rw [failed]
  rfl

theorem list_bound_failure (cap actual : NatOperand) (bits : Packed)
    (address capacity used : BitVec 64)
    (success : (countCall bits address capacity used).result = .ok actual)
    (over : ¬ actual.value ≤ cap.value) :
    measureList (some cap) bits (arenaState address capacity used) =
      ⟨.error (.limit cap actual), (countCall bits address capacity used).used,
        [countCall bits address capacity used]⟩ := by
  simp only [measureList, fromWide, arenaState, countCall, SszNative.Serialize.bind] at success ⊢
  rw [success]
  simp only [Except.mapError, bounded, over, ↓reduceIte, unchanged, List.append_nil]

theorem list_bound_pass (limit : Option NatOperand) (actual : NatOperand) (bits : Packed)
    (address capacity used : BitVec 64)
    (success : (countCall bits address capacity used).result = .ok actual)
    (fits : ∀ cap, limit = some cap → actual.value ≤ cap.value) :
    measureList limit bits (arenaState address capacity used) =
      ⟨(encodedCall bits address capacity used).result.mapError Error.arithmetic,
        (encodedCall bits address capacity used).used,
        [countCall bits address capacity used, encodedCall bits address capacity used]⟩ := by
  cases limit with
  | none =>
    simp only [measureList, fromWide, arenaState, countCall, encodedCall, encodedWide,
      SszNative.Serialize.bind] at success ⊢
    rw [success]
    rfl
  | some cap =>
    have bound := fits cap rfl
    simp only [measureList, fromWide, arenaState, countCall, encodedCall, encodedWide,
      SszNative.Serialize.bind] at success ⊢
    rw [success]
    simp only [Except.mapError, bounded, bound, ↓reduceIte, unchanged,
      List.nil_append, List.cons_append]

theorem count_call_value (bits : Packed) (address capacity used : BitVec 64)
    (actual : NatOperand) (success : (countCall bits address capacity used).result = .ok actual) :
    actual.value = bits.count.toNat :=
  NatArithmetic.fromWide_value _ _ _ _ _ success

theorem count_call_used_bound (bits : Packed) (address capacity used : BitVec 64) :
    (countCall bits address capacity used).used < 2^64 := by
  by_cases small : bits.count.toNat < 2^64
  · simp only [countCall, NatArithmetic.fromWide, small, ↓reduceIte, NatArithmetic.unchanged]
    exact used.isLt
  cases reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 with
  | none =>
    simp only [countCall, NatArithmetic.fromWide, small, ↓reduceIte, reserved, NatArithmetic.unchanged]
    exact used.isLt
  | some r =>
    obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
    simp only [countCall, NatArithmetic.fromWide, small, ↓reduceIte, reserved, NatArithmetic.committed]
    rw [shape]
    exact checks.2.2.2.2.1

theorem count_call_used_range (bits : Packed) (address capacity used : BitVec 64) :
    used.toNat ≤ (countCall bits address capacity used).used ∧
      ((countCall bits address capacity used).used = used.toNat ∨
        (countCall bits address capacity used).used ≤ capacity.toNat) := by
  refine ⟨wide_used_mono address.toNat capacity.toNat used.toNat bits.count, ?_⟩
  by_cases small : bits.count.toNat < 2^64
  · simp only [countCall, NatArithmetic.fromWide, small, ↓reduceIte, NatArithmetic.unchanged]
    exact Or.inl True.intro
  cases reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 with
  | none =>
    simp only [countCall, NatArithmetic.fromWide, small, ↓reduceIte, reserved, NatArithmetic.unchanged]
    exact Or.inl True.intro
  | some r =>
    obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
    simp only [countCall, NatArithmetic.fromWide, small, ↓reduceIte, reserved, NatArithmetic.committed]
    right
    rw [shape]
    exact checks.2.2.2.2.2

end SszX86.Measure.Bits
