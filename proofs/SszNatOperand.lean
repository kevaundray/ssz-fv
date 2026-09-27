import SszNatABI
import SszLimbOrder

set_option autoImplicit false

namespace SszNative

/-- A native natural's original representation, including redundant high limbs.
The pointer names borrowed storage; this executable model does not allocate it. -/
inductive NatOperand where
  | small (word : BitVec 64)
  | large (pointer : BitVec 64) (words : List (BitVec 64))
  deriving DecidableEq, Repr

namespace NatOperand

def words : NatOperand → List (BitVec 64)
  | .small word => [word]
  | .large _ limbs => limbs

def value (operand : NatOperand) : Nat := Limbs.value operand.words

def pointer : NatOperand → BitVec 64
  | .small _ => 0#64
  | .large address _ => address

def payload : NatOperand → BitVec 64
  | .small word => word
  | .large _ limbs => BitVec.ofNat 64 limbs.length

def wordCount (operand : NatOperand) : Nat := Limbs.sigWords operand.words

/-- Native from_words: retain the original pointer only for a multiword result. -/
def fromWords (address : BitVec 64) (limbs : List (BitVec 64)) : NatOperand :=
  match Limbs.trim limbs with
  | [] => .small 0#64
  | [word] => .small word
  | first :: second :: rest => .large address (first :: second :: rest)

def normalized (operand : NatOperand) : NatOperand :=
  fromWords operand.pointer operand.words

/-- The exact supplied limbs, not merely some equal-valued representation.
Read-only separation and allocator ownership remain the ISA caller's obligations. -/
def At (observe : Nat → Nat → Option Nat) : NatOperand → Prop
  | .small _ => True
  | .large address limbs =>
    0 < address.toNat ∧ address.toNat % 8 = 0 ∧
      address.toNat + 8 * limbs.length ≤ 2^64 ∧
      NatMemory.wordsAt observe address.toNat limbs

theorem At.pair (observe : Nat → Nat → Option Nat) (operand : NatOperand)
    (owned : operand.At observe) :
    NatMemory.Pair observe operand.pointer operand.payload operand.value := by
  cases operand with
  | small word =>
    exact Or.inl ⟨rfl, by
      simp only [payload, value, words, Limbs.value, Nat.mul_zero, Nat.add_zero]⟩
  | large address limbs =>
    obtain ⟨positive, aligned, bound, stored⟩ := owned
    have count : limbs.length < 2^64 := by omega
    exact Or.inr ⟨limbs, positive, aligned, bound,
      by simp only [payload, BitVec.toNat_ofNat, Nat.mod_eq_of_lt count], stored, rfl⟩

theorem fromWords_value (address : BitVec 64) (limbs : List (BitVec 64)) :
    (fromWords address limbs).value = Limbs.value limbs := by
  have same := Limbs.trim_value limbs
  cases trimmed : Limbs.trim limbs with
  | nil => simpa only [trimmed, fromWords, value, words, Limbs.value,
      BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero] using same
  | cons first rest =>
    cases rest with
    | nil => simpa only [trimmed, fromWords, value, words] using same
    | cons second rest => simpa only [trimmed, fromWords, value, words] using same

theorem normalized_value (operand : NatOperand) : operand.normalized.value = operand.value :=
  fromWords_value operand.pointer operand.words

theorem wordCount_eq_trim_length (operand : NatOperand) :
    operand.wordCount = (Limbs.trim operand.words).length :=
  (Limbs.trim_length operand.words).symm

end NatOperand
end SszNative
