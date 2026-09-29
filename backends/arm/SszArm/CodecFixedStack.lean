import SszCodecTypes

namespace SszArm.Codec.Fixed

open SszNative.Codec (Desc)

mutual
  /-- is_fixed follows vector chains in its current 32-byte activation.
  A field call uses a fresh activation; the local lowered bit-test needs 16
  additional bytes only after that call has returned. -/
  def isFixedStack : Desc → Nat
    | .vector element _ => isFixedStack element
    | .container fields | .progressiveContainer _ fields =>
        32 + max 16 (isFixedFieldsStack fields)
    | _ => 32

  def isFixedFieldsStack : List (String × Desc) → Nat
    | [] => 0
    | (_, field) :: rest => max (isFixedStack field) (isFixedFieldsStack rest)
end

mutual
  /-- measure_fixed has a 160-byte activation and a 16-byte lowering spill.
  The existing Nat providers require 80 bytes for division, 16 for addition,
  and 144 for multiplication; memcpy adds no stack allocation. -/
  def measureFixedStack : Desc → Nat
    | .primitive (.bitVector _) => 240
    | .vector element _ => 160 + max 144 (measureFixedStack element)
    | .container fields | .progressiveContainer _ fields =>
        160 + max 16 (measureFixedFieldsStack fields)
    | _ => 176

  def measureFixedFieldsStack : List (String × Desc) → Nat
    | [] => 0
    | (_, field) :: rest => max (measureFixedStack field) (measureFixedFieldsStack rest)
end

theorem isFixedStack_activation (desc : Desc) : 32 ≤ isFixedStack desc := by
  cases desc with
  | vector element length => exact isFixedStack_activation element
  | container fields | progressiveContainer active fields =>
    simp only [isFixedStack]
    omega
  | _ => simp only [isFixedStack, Nat.le_refl]

theorem measureFixedStack_activation (desc : Desc) : 176 ≤ measureFixedStack desc := by
  cases desc with
  | primitive shape => cases shape <;> simp [measureFixedStack]
  | vector element length => simp only [measureFixedStack]; omega
  | container fields | progressiveContainer active fields =>
    simp only [measureFixedStack]
    omega
  | _ => simp only [measureFixedStack, Nat.le_refl]

theorem isFixedFieldsStack_head (name : String) (desc : Desc)
    (rest : List (String × Desc)) :
    isFixedStack desc ≤ isFixedFieldsStack ((name, desc) :: rest) :=
  Nat.le_max_left _ _

theorem isFixedFieldsStack_tail (name : String) (desc : Desc)
    (rest : List (String × Desc)) :
    isFixedFieldsStack rest ≤ isFixedFieldsStack ((name, desc) :: rest) :=
  Nat.le_max_right _ _

theorem measureFixedFieldsStack_head (name : String) (desc : Desc)
    (rest : List (String × Desc)) :
    measureFixedStack desc ≤ measureFixedFieldsStack ((name, desc) :: rest) :=
  Nat.le_max_left _ _

theorem measureFixedFieldsStack_tail (name : String) (desc : Desc)
    (rest : List (String × Desc)) :
    measureFixedFieldsStack rest ≤ measureFixedFieldsStack ((name, desc) :: rest) :=
  Nat.le_max_right _ _

theorem isFixedStack_vector (desc : Desc) (length : SszNative.NatOperand) :
    isFixedStack (.vector desc length) = isFixedStack desc := rfl

theorem measureFixedStack_vector (desc : Desc) (length : SszNative.NatOperand) :
    160 + measureFixedStack desc ≤ measureFixedStack (.vector desc length) := by
  simp only [measureFixedStack]
  omega

end SszArm.Codec.Fixed
