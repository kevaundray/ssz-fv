import SszFixedSize
import SszFixed

namespace SszNative.FixedSize

mutual
  theorem isFixed_erase (desc : Codec.Desc) :
      isFixed desc = Fixed.classify desc.erase := by
    cases desc with
    | primitive shape => cases shape <;> rfl
    | vector element length => exact isFixed_erase element
    | container fields => exact fieldsFixed_erase fields
    | progressiveContainer active fields => exact fieldsFixed_erase fields
    | _ => rfl

  theorem fieldsFixed_erase (fields : List (String × Codec.Desc)) :
      fieldsFixed fields = Fixed.classifyFields (Codec.Desc.eraseFields fields) := by
    cases fields with
    | nil => rfl
    | cons field rest =>
      rcases field with ⟨name, shape⟩
      simp only [fieldsFixed, Codec.Desc.eraseFields, Fixed.classifyFields,
        isFixed_erase shape, fieldsFixed_erase rest]
end

/-- Structural classification agrees with upstream on every raw declaration,
including empty containers, invalid uint widths, and arbitrary active masks. -/
theorem isFixed_eq (desc : Codec.Desc) :
    isFixed desc = desc.erase.fixedSize.isSome := by
  rw [isFixed_erase, Fixed.classify_eq]

theorem isFixed_isFixed (desc : Codec.Desc) :
    isFixed desc = desc.erase.isFixed := isFixed_eq desc

theorem isFixed_false_iff (desc : Codec.Desc) :
    isFixed desc = false ↔ desc.erase.fixedSize = none := by
  rw [isFixed_eq]
  cases desc.erase.fixedSize <;> simp

/-- The result, original cursor, and empty trace are fixed before entering the
measurement recursion; scratch exhaustion in any fixed prefix is irrelevant. -/
theorem fixedSize_variable (desc : Codec.Desc) (arena : Delimited.ArenaState)
    (notFixed : isFixed desc = false) :
    fixedSize desc arena = Serialize.unchanged arena.used (.ok none) := by
  simp only [fixedSize, notFixed, Bool.false_eq_true, ↓reduceIte]

theorem fixedSize_fixed (desc : Codec.Desc) (arena : Delimited.ArenaState)
    (fixed : isFixed desc = true) :
    fixedSize desc arena = measureFixed desc arena := by
  simp only [fixedSize, fixed, ↓reduceIte]

theorem fixedSize_variable_vector (element : Codec.Desc) (length : NatOperand)
    (arena : Delimited.ArenaState) (notFixed : isFixed element = false) :
    fixedSize (.vector element length) arena =
      Serialize.unchanged arena.used (.ok none) :=
  fixedSize_variable _ arena notFixed

/-- These leaves borrow the exact original operand, not its normalization. -/
theorem fixedSize_uint (width : NatOperand) (arena : Delimited.ArenaState) :
    fixedSize (.primitive (.uint width)) arena =
      Serialize.unchanged arena.used (.ok (some width)) := rfl

theorem fixedSize_byteVector (length : NatOperand) (arena : Delimited.ArenaState) :
    fixedSize (.primitive (.byteVector length)) arena =
      Serialize.unchanged arena.used (.ok (some length)) := rfl

end SszNative.FixedSize
