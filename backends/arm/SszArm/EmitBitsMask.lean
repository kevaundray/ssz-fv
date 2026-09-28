import SszArm.EmitBitsFacts

namespace SszArm.Emit.Bits

/-- The low byte of the actual 32-bit BIC after shifting all ones. -/
def maskByte (byte : BitVec 8) (remainder : Nat) : BitVec 8 :=
  ((byte.setWidth 32) &&& ~~~(4294967295#32 <<< remainder)).setWidth 8

/-- The list path ORs in exactly the first bit after the data, not an input
padding bit. This definition also covers the aligned/empty delimiter value. -/
def delimiterByte (byte : BitVec 8) (remainder : Nat) : BitVec 8 :=
  maskByte byte remainder ||| (1#8 <<< remainder)

theorem maskByte_eq (byte : UInt8) (remainder : Nat) (small : remainder < 8) :
    maskByte byte.toBitVec remainder =
      (byte &&& UInt8.ofNat (2 ^ remainder - 1)).toBitVec := by
  have choices : remainder = 0 ∨ remainder = 1 ∨ remainder = 2 ∨ remainder = 3 ∨
      remainder = 4 ∨ remainder = 5 ∨ remainder = 6 ∨ remainder = 7 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) [maskByte, BitVec.setWidth_and]

theorem delimiterByte_eq (byte : UInt8) (remainder : Nat) (small : remainder < 8) :
    delimiterByte byte.toBitVec remainder =
      ((byte &&& UInt8.ofNat (2 ^ remainder - 1)) |||
        (1 <<< UInt8.ofNat remainder)).toBitVec := by
  rw [delimiterByte, maskByte_eq byte remainder small]
  have choices : remainder = 0 ∨ remainder = 1 ∨ remainder = 2 ∨ remainder = 3 ∨
      remainder = 4 ∨ remainder = 5 ∨ remainder = 6 ∨ remainder = 7 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true})

@[simp] theorem delimiterByte_zero (byte : BitVec 8) : delimiterByte byte 0 = 1#8 := by
  simp [delimiterByte, maskByte]

end SszArm.Emit.Bits
