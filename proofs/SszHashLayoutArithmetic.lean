import SszHashLayoutTypes

set_option autoImplicit false

namespace SszNative.HashLayout

/-- Only the error wrapper changes; successful raw operands are retained. -/
def arithmeticResult {α : Type} : Except NatArithmetic.Failure α → Except Error α
  | .ok value => .ok value
  | .error reason => .error (arithmeticError reason)

def fromWide (wide : BitVec 128) (arena : Delimited.ArenaState) : Outcome NatOperand :=
  let outcome := NatArithmetic.fromWide arena.base arena.capacity arena.used wide
  ⟨arithmeticResult outcome.result, outcome.used, [.fromWide wide arena outcome]⟩

def add (left right : NatOperand) (arena : Delimited.ArenaState) : Outcome NatOperand :=
  let outcome := NatAdd.run left right arena.base arena.capacity arena.used
  ⟨arithmeticResult outcome.result, outcome.used, [.add left right arena outcome]⟩

def mul (left right : NatOperand) (arena : Delimited.ArenaState) : Outcome NatOperand :=
  let outcome := NatMul.run left right arena.base arena.capacity arena.used
  ⟨arithmeticResult outcome.result, outcome.used, [.mul left right arena outcome]⟩

def divide (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) : Outcome (NatOperand × BitVec 64) :=
  let outcome := NatDivision.run operand divisor arena.base arena.capacity arena.used
  ⟨arithmeticResult outcome.result, outcome.used, [.divide operand divisor arena outcome]⟩

/-- Native layout.rs:40–43: division first, then ONE addition only on a remainder.
No speculative addition, mathematical operand cap, or scratch precheck occurs. -/
def ceilDiv (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) : Outcome NatOperand :=
  bind (divide operand divisor arena) fun divided used =>
    if divided.2 = 0 then unchanged used (.ok divided.1)
    else add divided.1 (.small 1) { arena with used := used }

/-- Exactly two raw limb writes into the zero-initialized destination: no
from_u128 conversion, normalization, or arena allocation is performed. -/
def countWord128 (wide : BitVec 128) : Ssz.Bytes :=
  MerkleWords.lengthLoop (.large 0 [wide.setWidth 64, (wide >>> 64).setWidth 64]) 2

@[simp] theorem arithmeticResult_ok_iff {α : Type}
    (result : Except NatArithmetic.Failure α) (value : α) :
    arithmeticResult result = .ok value ↔ result = .ok value := by
  cases result <;> simp [arithmeticResult]

@[simp] theorem arithmeticResult_error_iff {α : Type}
    (result : Except NatArithmetic.Failure α) (reason : Error) :
    arithmeticResult result = .error reason ↔
      ∃ failure, result = .error failure ∧ arithmeticError failure = reason := by
  cases result <;> simp [arithmeticResult]

 theorem fromWide_value (wide : BitVec 128) (arena : Delimited.ArenaState)
    (result : NatOperand) (success : (fromWide wide arena).result = .ok result) :
    result.value = wide.toNat :=
  NatArithmetic.fromWide_value _ _ _ _ _ ((arithmeticResult_ok_iff _ _).mp success)

 theorem add_value (left right : NatOperand) (arena : Delimited.ArenaState)
    (result : NatOperand) (success : (add left right arena).result = .ok result) :
    result.value = left.value + right.value :=
  NatAdd.run_value _ _ _ _ _ _ ((arithmeticResult_ok_iff _ _).mp success)

 theorem mul_value (left right : NatOperand) (arena : Delimited.ArenaState)
    (result : NatOperand) (success : (mul left right arena).result = .ok result) :
    result.value = left.value * right.value :=
  NatMul.run_value _ _ _ _ _ _ ((arithmeticResult_ok_iff _ _).mp success)

 theorem divide_value (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) (result : NatOperand × BitVec 64)
    (success : (divide operand divisor arena).result = .ok result) :
    result.1.value = operand.value / divisor.toNat ∧
      result.2.toNat = operand.value % divisor.toNat ∧ result.2.toNat < divisor.toNat :=
  NatDivision.run_success _ _ _ _ _ _ ((arithmeticResult_ok_iff _ _).mp success)

/-- The full failed division attempt is retained; addition is never attempted. -/
theorem ceilDiv_division_error (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) (reason : Error)
    (failed : (divide operand divisor arena).result = .error reason) :
    ceilDiv operand divisor arena =
      ⟨.error reason, (divide operand divisor arena).used,
        (divide operand divisor arena).effects⟩ := by
  simp only [ceilDiv, bind, failed]

/-- The exact successful division/zero remainder phase retains its entire trace. -/
theorem ceilDiv_exact (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) (quotient : NatOperand)
    (success : (divide operand divisor arena).result = .ok (quotient, 0)) :
    ceilDiv operand divisor arena =
      ⟨.ok quotient, (divide operand divisor arena).used,
        (divide operand divisor arena).effects⟩ := by
  simp only [ceilDiv, bind, success, ↓reduceIte, unchanged, List.append_nil]

/-- Nonzero remainder performs precisely one addition, at the committed division
cursor; even an addition failure retains both attempted operations in order. -/
theorem ceilDiv_increment (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) (quotient : NatOperand) (remainder : BitVec 64)
    (success : (divide operand divisor arena).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0) :
    ceilDiv operand divisor arena =
      let second := add quotient (.small 1)
        { arena with used := (divide operand divisor arena).used }
      ⟨second.result, second.used, (divide operand divisor arena).effects ++ second.effects⟩ := by
  simp only [ceilDiv, bind, success, nonzero, ↓reduceIte]

/-- The quotient/remainder characterization of ceiling division, for every
positive natural divisor rather than just the native callers' 32 and 256. -/
theorem ceiling_identity (number divisor : Nat) (positive : 0 < divisor) :
    (if number % divisor = 0 then number / divisor else number / divisor + 1) =
      (number + divisor - 1) / divisor := by
  have decomposition := Nat.mod_add_div number divisor
  have bounded := Nat.mod_lt number positive
  by_cases zero : number % divisor = 0
  · simp only [zero, ↓reduceIte]
    symm
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm]
      omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (number / divisor) divisor]
      omega
  · simp only [zero, ↓reduceIte]
    symm
    apply Nat.div_eq_of_lt_le
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (number / divisor) divisor]
      omega
    · rw [Nat.add_mul, Nat.add_mul, Nat.one_mul,
        Nat.mul_comm (number / divisor) divisor]
      omega

 theorem ceilDiv_value (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) (nonzero : divisor ≠ 0) (result : NatOperand)
    (success : (ceilDiv operand divisor arena).result = .ok result) :
    result.value = (operand.value + divisor.toNat - 1) / divisor.toNat := by
  have positive : 0 < divisor.toNat := by
    have : divisor.toNat ≠ 0 := by
      intro zero
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      simpa using zero
    omega
  rw [← ceiling_identity _ _ positive]
  cases divided : (divide operand divisor arena).result with
  | error reason =>
    rw [ceilDiv_division_error operand divisor arena reason divided] at success
    cases success
  | ok pair =>
    obtain ⟨quotient, remainder⟩ := pair
    have values := divide_value operand divisor arena (quotient, remainder) divided
    by_cases zero : remainder = 0
    · subst remainder
      rw [ceilDiv_exact operand divisor arena quotient divided] at success
      cases success
      have remainderZero : operand.value % divisor.toNat = 0 := by
        simpa using values.2.1.symm
      simp only [remainderZero, ↓reduceIte, values.1]
    · rw [ceilDiv_increment operand divisor arena quotient remainder divided zero] at success
      have sum := add_value quotient (.small 1)
        { arena with used := (divide operand divisor arena).used } result success
      have remainderNonzero : operand.value % divisor.toNat ≠ 0 := by
        intro remainderZero
        apply zero
        apply BitVec.eq_of_toNat_eq
        change remainder.toNat = 0
        exact values.2.1.trans remainderZero
      have one : (NatOperand.small (1 : BitVec 64)).value = 1 := rfl
      rw [one, values.1] at sum
      simpa only [remainderNonzero, ↓reduceIte] using sum

@[simp] theorem countWord128_size (wide : BitVec 128) : (countWord128 wide).size = 32 :=
  MerkleWords.lengthLoop_size _ _

private theorem bytes_ext (left right : Ssz.Bytes) (sized : left.size = right.size)
    (same : ∀ index, index < left.size → left[index]! = right[index]!) : left = right := by
  apply Array.ext sized
  intro index inside otherInside
  simpa only [getElem!_pos, inside, otherInside] using same index inside

 theorem countWord128_eq_lengthWord (wide : BitVec 128) :
    countWord128 wide = Ssz.lengthWord wide.toNat := by
  apply bytes_ext
  · simp [Ssz.lengthWord, Ssz.bytesPerChunk, Ssz.uintBytes_size]
  · intro index inside
    have small : index < 32 := by simpa only [countWord128_size] using inside
    change (MerkleWords.lengthLoop
      (.large 0 [wide.setWidth 64, (wide >>> 64).setWidth 64]) 2)[index]! = _
    rw [MerkleWords.lengthLoop_get _ 2 index small]
    have byte : (Ssz.lengthWord wide.toNat)[index]! =
        UInt8.ofNat ((wide.toNat / 2 ^ (8 * index)) % 256) := by
      simpa only [Ssz.lengthWord, Ssz.bytesPerChunk, getElem!_pos,
        Ssz.uintBytes_size, small] using Limbs.uintBytes_byte 32 wide.toNat index small
    rw [byte]
    change (if index < 8 * 2 then
      Limbs.byteAt [wide.setWidth 64, (wide >>> 64).setWidth 64] index else 0) = _
    simp only [Limbs.byteAt_eq_value, NatArithmetic.wide_words_value]
    split
    · rfl
    · rename_i beyond
      have power : 2 ^ 128 ≤ 2 ^ (8 * index) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have bounded : wide.toNat < 2 ^ (8 * index) := Nat.lt_of_lt_of_le wide.isLt power
      simp [Nat.div_eq_of_lt bounded]

end SszNative.HashLayout
