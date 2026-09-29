import SszCodecTypes
import SszX86.DelimitedCore

namespace SszX86.CodecMeasureFixed
open SszNative

mutual
  /-- Six saved words and 88 local bytes make a 136-byte activation. CALL adds
  eight bytes. Reused arithmetic providers need 48 (add), 64 (division including
  its lowering call), or 96 (mul including memset) further stack bytes. -/
  def stackBytes : Codec.Desc → Nat
    | .primitive (.bitVector _) => 136 + 8 + 64
    | .vector element _ => 136 + 8 + max (stackBytes element) 96
    | .container fields | .progressiveContainer _ fields => 136 + fieldsStackBytes fields
    | _ => 136

  /-- Fields are sequential, not simultaneously live recursive activations.
  Their measurement returns before the checked addition of the running width. -/
  def fieldsStackBytes : List (String × Codec.Desc) → Nat
    | [] => 0
    | (_, field) :: rest => max (8 + max (stackBytes field) 48) (fieldsStackBytes rest)
end

theorem stackBytes_activation (desc : Codec.Desc) : 136 ≤ stackBytes desc := by
  cases desc with
  | primitive shape => cases shape <;> simp only [stackBytes] <;> omega
  | vector element length => simp only [stackBytes]; omega
  | container fields => simp only [stackBytes]; omega
  | progressiveContainer active fields => simp only [stackBytes]; omega
  | _ => exact Nat.le_refl _

theorem vector_recursive_stack (element : Codec.Desc) (length : NatOperand) :
    144 + stackBytes element ≤ stackBytes (.vector element length) := by
  have := Nat.le_max_left (stackBytes element) 96
  simp only [stackBytes]
  omega

theorem vector_multiply_stack (element : Codec.Desc) (length : NatOperand) :
    144 + 96 ≤ stackBytes (.vector element length) := by
  have := Nat.le_max_right (stackBytes element) 96
  simp only [stackBytes]
  omega

theorem fields_recursive_stack (name : String) (field : Codec.Desc)
    (rest : List (String × Codec.Desc)) :
    8 + stackBytes field ≤ fieldsStackBytes ((name, field) :: rest) := by
  have := Nat.le_max_left (stackBytes field) 48
  have := Nat.le_max_left (8 + max (stackBytes field) 48) (fieldsStackBytes rest)
  simp only [fieldsStackBytes]
  omega

theorem fields_add_stack (name : String) (field : Codec.Desc)
    (rest : List (String × Codec.Desc)) :
    8 + 48 ≤ fieldsStackBytes ((name, field) :: rest) := by
  have := Nat.le_max_right (stackBytes field) 48
  have := Nat.le_max_left (8 + max (stackBytes field) 48) (fieldsStackBytes rest)
  simp only [fieldsStackBytes]
  omega

theorem fields_tail_stack (name : String) (field : Codec.Desc)
    (rest : List (String × Codec.Desc)) :
    fieldsStackBytes rest ≤ fieldsStackBytes ((name, field) :: rest) :=
  Nat.le_max_right _ _

structure StackOwned (m : DataMem) (sp : BitVec 64) (desc : Codec.Desc) : Prop where
  low : stackBytes desc ≤ sp.toNat
  bound : sp.toNat + 8 ≤ 2 ^ 64
  «mapped» : UintCodec.Large.Mapped m (sp - BitVec.ofNat 64 (stackBytes desc))
    (stackBytes desc + 8)

end SszX86.CodecMeasureFixed
