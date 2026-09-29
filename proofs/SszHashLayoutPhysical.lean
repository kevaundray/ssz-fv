import SszHashLayoutGenerated
import SszHashLayoutPackedProofs

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

 theorem sequence_count_physical (element : Desc) (values : List Value)
    (positions : Option NatOperand) (mixin : Option Ssz.Bytes) (arena : Delimited.ArenaState)
    (view : Layout) (physical : values.length < 2 ^ 64)
    (success : (sequence element values positions mixin arena).result = .ok view) :
    view.count < 2 ^ 64 := by
  simp only [sequence, lift, bind, unchanged] at success
  repeat' first | split at success | cases success
  all_goals first
    | exact physical
    | exact packed_count_basic_physical values _ physical
        (basicWidth_bound element _ (by assumption))

/-- The physical leaf count is derived from generated views. Logical capacities
are absent from this bound, including when their represented value exceeds 2^64. -/
theorem layout_count_physical (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (view : Layout) (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (success : (layout desc value arena).result = .ok view) : view.count < 2 ^ 64 := by
  cases desc with
  | primitive shape =>
      cases shape with
      | bool | uint _ =>
          simp only [layout, lift, bind, unchanged] at success
          repeat first | split at success | cases success
          all_goals apply packed_count_scalar_physical
          all_goals exact basicWidth_bound _ _ (scalar_basicWidth _ _ _ _ (by assumption))
      | byteVector length =>
          cases value <;> simp only [layout, unchanged] at success
          repeat' first | split at success | cases success
          all_goals exact packed_count_bytes_physical _ valuePhysical
      | byteList limit =>
          cases value <;> simp only [layout, bind, unchanged] at success
          all_goals repeat first | split at success | cases success
          all_goals exact packed_count_bytes_physical _ valuePhysical
      | bitVector length | bitList length =>
          cases value <;> simp only [layout, bind, unchanged] at success
          repeat' first | split at success | cases success
          all_goals exact packed_count_bits_physical _ valuePhysical
      | progressiveBitList limit =>
          cases value <;> simp only [layout, unchanged] at success
          all_goals cases success
          all_goals exact packed_count_bits_physical _ valuePhysical
  | vector element length =>
      cases value <;> simp only [layout, unchanged] at success
      all_goals first
        | cases success
        | split at success
      all_goals first
        | cases success
        | exact sequence_count_physical element _ _ _ arena view valuePhysical.1 success
  | list element limit =>
      cases value <;> simp only [layout, unchanged] at success
      all_goals first
        | cases success
        | split at success
      all_goals first
        | cases success
        | exact sequence_count_physical element _ _ _ arena view valuePhysical.1 success
  | progressiveList element limit =>
      cases value <;> simp only [layout, unchanged] at success
      all_goals first
        | cases success
        | exact sequence_count_physical element _ _ _ arena view valuePhysical.1 success
  | container fields =>
      cases value <;> simp only [layout, unchanged] at success
      repeat' first | split at success | cases success
      all_goals exact valuePhysical.1
  | progressiveContainer active fields =>
      cases value <;> simp only [layout, unchanged] at success
      repeat' first | split at success | cases success
      all_goals exact descPhysical.1
  | compatibleUnion options =>
      cases value <;> simp only [layout, unchanged] at success
      all_goals repeat first | split at success | cases success
      all_goals change 1 < 2 ^ 64
      all_goals decide

end SszNative.HashLayout
