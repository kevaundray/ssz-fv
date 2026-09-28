import SszX86.MeasureCore

namespace SszX86.Measure.Bytes
open SszNative SszNative.Serialize

/-- Byte vectors return the physical byte count, never a canonicalized width. -/
theorem vector_measure (operand : NatOperand) (data : Ssz.Bytes)
    (arena : Delimited.ArenaState) :
    measure (.byteVector operand) (.bytes data) arena =
      if operand.value = data.size then unchanged arena.used (.ok (count data.size))
      else unchanged arena.used (.error (.scope operand (count data.size))) := rfl

/-- A byte list's bounded check does not invoke a constructor or commit scratch.
Only its physical byte count is machine-sized; the logical cap is unrestricted. -/
theorem list_measure (operand : NatOperand) (data : Ssz.Bytes)
    (physical : data.size < 2^64) (arena : Delimited.ArenaState) :
    measure (.byteList operand) (.bytes data) arena =
      if data.size ≤ operand.value then unchanged arena.used (.ok (count data.size))
      else unchanged arena.used (.error (.limit operand (count data.size))) := by
  by_cases fits : data.size ≤ operand.value <;>
    simp [SszNative.Serialize.measure, bounded, count_value data.size physical, fits,
      SszNative.Serialize.bind, unchanged]

/-- The original cursor survives all byte-vector results, including invalid arenas. -/
theorem vector_noalloc (operand : NatOperand) (value : Value) (arena : Delimited.ArenaState) :
    (measure (.byteVector operand) value arena).used = arena.used ∧
      (measure (.byteVector operand) value arena).calls = [] := by
  cases value with
  | bytes data =>
    by_cases fits : operand.value = data.size <;>
      simp only [vector_measure, fits, ↓reduceIte, unchanged, and_self]
  | _ => exact ⟨rfl, rfl⟩

/-- The original cursor survives all byte-list results, including invalid arenas. -/
theorem list_noalloc (operand : NatOperand) (value : Value) (arena : Delimited.ArenaState) :
    (measure (.byteList operand) value arena).used = arena.used ∧
      (measure (.byteList operand) value arena).calls = [] := by
  cases value with
  | bytes data =>
    by_cases fits : (count data.size).value ≤ operand.value <;>
      simp [SszNative.Serialize.measure, bounded, fits, SszNative.Serialize.bind, unchanged]
  | _ => exact ⟨rfl, rfl⟩

end SszX86.Measure.Bytes
