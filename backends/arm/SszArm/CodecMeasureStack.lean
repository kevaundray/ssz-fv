import SszArm.CodecFixedStack
import SszCodecMeasure

set_option autoImplicit false

namespace SszArm.Codec.Measure

open SszNative.Codec (Desc)

/-- measure_parts has a 400-byte activation. Each callback has a 240-byte
activation and calls both measure and is_fixed; its Nat.add and lowering
scratch require sixteen bytes. Sequential children reuse the same activation. -/
def partsStackFor (fixed child : Nat) : Nat :=
  400 + max 16 (max fixed (240 + max 16 (max fixed child)))

mutual
  /-- Stack usage follows the actual descriptor calls, not a fixed depth cap.
  Union adds its 272-byte activation to either a recursive child, the 48-byte
  singleton allocator, or the 16-byte Nat/add/lowering requirement. -/
  def stackBytes : Desc → Nat
    | .primitive _ => 288
    | .vector element _ | .list element _ | .progressiveList element _ =>
        272 + partsStackFor (Fixed.isFixedStack element) (stackBytes element)
    | .container fields | .progressiveContainer _ fields =>
        272 + partsStackFor (Fixed.isFixedFieldsStack fields) (fieldsStack fields)
    | .compatibleUnion variants => 272 + max 48 (variantsStack variants)

  def fieldsStack : List (String × Desc) → Nat
    | [] => 0
    | (_, field) :: rest => max (stackBytes field) (fieldsStack rest)

  def variantsStack : List (SszNative.NatOperand × Desc) → Nat
    | [] => 0
    | (_, child) :: rest => max (stackBytes child) (variantsStack rest)
end

def childStack (desc : Desc) : Nat :=
  240 + max 16 (max (Fixed.isFixedStack desc) (stackBytes desc))

def partsStack : SszNative.CodecMeasure.Parts → Nat
  | .repeated element => partsStackFor (Fixed.isFixedStack element) (stackBytes element)
  | .fields fields => partsStackFor (Fixed.isFixedFieldsStack fields) (fieldsStack fields)

theorem stackBytes_activation (desc : Desc) : 288 ≤ stackBytes desc := by
  cases desc <;> simp only [stackBytes, partsStackFor] <;> omega

theorem partsStackFor_callback (fixed child : Nat) :
    400 + (240 + max 16 (max fixed child)) ≤ partsStackFor fixed child := by
  unfold partsStackFor
  omega

theorem partsStackFor_fixed (fixed child : Nat) :
    400 + fixed ≤ partsStackFor fixed child := by
  unfold partsStackFor
  omega

theorem fieldsStack_head (name : String) (desc : Desc) (rest : List (String × Desc)) :
    stackBytes desc ≤ fieldsStack ((name, desc) :: rest) := Nat.le_max_left _ _

theorem fieldsStack_tail (name : String) (desc : Desc) (rest : List (String × Desc)) :
    fieldsStack rest ≤ fieldsStack ((name, desc) :: rest) := Nat.le_max_right _ _

theorem variantsStack_head (selector : SszNative.NatOperand) (desc : Desc)
    (rest : List (SszNative.NatOperand × Desc)) :
    stackBytes desc ≤ variantsStack ((selector, desc) :: rest) := Nat.le_max_left _ _

theorem variantsStack_tail (selector : SszNative.NatOperand) (desc : Desc)
    (rest : List (SszNative.NatOperand × Desc)) :
    variantsStack rest ≤ variantsStack ((selector, desc) :: rest) := Nat.le_max_right _ _

end SszArm.Codec.Measure
