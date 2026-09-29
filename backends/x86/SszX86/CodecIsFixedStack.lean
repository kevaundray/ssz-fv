import SszCodecTypes
import SszX86.DelimitedCore

namespace SszX86.CodecIsFixed
open SszNative

mutual
  /-- Three pushes use 24 bytes. A vector follows its element in the same
  activation. Only field visits make CALLs, each adding an eight-byte return
  slot. Widths, limits, masks and names do not contribute to this bound. -/
  def stackBytes : Codec.Desc → Nat
    | .vector element _ => stackBytes element
    | .container fields | .progressiveContainer _ fields => 24 + fieldsStackBytes fields
    | _ => 24

  def fieldsStackBytes : List (String × Codec.Desc) → Nat
    | [] => 0
    | (_, field) :: rest => max (8 + stackBytes field) (fieldsStackBytes rest)
end

theorem stackBytes_activation (desc : Codec.Desc) : 24 ≤ stackBytes desc := by
  cases desc with
  | vector element length => exact stackBytes_activation element
  | container fields => simp only [stackBytes]; omega
  | progressiveContainer active fields => simp only [stackBytes]; omega
  | _ => exact Nat.le_refl _

/-- At PC109 the recursive callee enters at parentSP-32. Its entire finite
activation fits below the parent's three saved words. -/
theorem fieldsStackBytes_head (name : String) (field : Codec.Desc)
    (rest : List (String × Codec.Desc)) :
    8 + stackBytes field ≤ fieldsStackBytes ((name, field) :: rest) := by
  exact Nat.le_max_left _ _

theorem fieldsStackBytes_tail (name : String) (field : Codec.Desc)
    (rest : List (String × Codec.Desc)) :
    fieldsStackBytes rest ≤ fieldsStackBytes ((name, field) :: rest) := by
  exact Nat.le_max_right _ _

theorem container_child_stack (sp : Nat) (name : String) (field : Codec.Desc)
    (rest : List (String × Codec.Desc))
    (low : stackBytes (.container ((name, field) :: rest)) ≤ sp) :
    stackBytes field ≤ sp - 32 ∧
    sp - stackBytes (.container ((name, field) :: rest)) ≤
      sp - 32 - stackBytes field := by
  have head := fieldsStackBytes_head name field rest
  simp only [stackBytes] at low ⊢
  omega

/-- Physical stack ownership is finite and descriptor-indexed, rather than a
fixed leaf budget silently reused for arbitrarily deep recursive calls. -/
structure StackOwned (m : DataMem) (sp : BitVec 64) (desc : Codec.Desc) : Prop where
  low : stackBytes desc ≤ sp.toNat
  bound : sp.toNat + 8 ≤ 2 ^ 64
  «mapped» : UintCodec.Large.Mapped m (sp - BitVec.ofNat 64 (stackBytes desc))
    (stackBytes desc + 8)

end SszX86.CodecIsFixed
