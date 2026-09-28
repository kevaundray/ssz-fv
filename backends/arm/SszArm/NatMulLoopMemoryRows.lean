import SszArm.NatMulLoopMemory

namespace SszArm.NatMul

open SszNative (LimbMul)

/-- A row replaces its inner words and its carry cell, retaining the suffix. -/
theorem nativeRow_length (factor : BitVec 64) (right buffer : List (BitVec 64))
    (room : right.length + 1 ≤ buffer.length) :
    (LimbMul.nativeRow factor right buffer).length = buffer.length := by
  simp only [LimbMul.nativeRow, List.length_append, LimbMul.row_length, List.length_drop]
  omega

/-- Every native row shortens the active window by exactly its finalized head. -/
theorem nativeRows_length (left right buffer : List (BitVec 64))
    (room : left.length + right.length ≤ buffer.length) :
    (LimbMul.nativeRows left right buffer).length = buffer.length := by
  induction left generalizing buffer with
  | nil => rfl
  | cons factor left ih =>
    have rowRoom : right.length + 1 ≤ buffer.length := by
      simp only [List.length_cons] at room
      omega
    have rowLength := nativeRow_length factor right buffer rowRoom
    have tailRoom : left.length + right.length ≤
        (LimbMul.nativeRow factor right buffer).tail.length := by
      simp only [List.length_tail, rowLength]
      simp only [List.length_cons] at room
      omega
    simp only [LimbMul.nativeRows, List.length_cons, ih _ tailRoom,
      List.length_tail, rowLength]
    omega

/-- The native inner-loop stores are exactly the low prefix of nativeRow. -/
theorem nativeRow_inner (factor : BitVec 64) (right buffer : List (BitVec 64)) :
    (LimbMul.nativeRow factor right buffer).take right.length =
      (LimbMul.inner right.length factor right buffer 0).1 := by
  have len := LimbMul.inner_length right.length factor right buffer 0
  unfold LimbMul.nativeRow LimbMul.row
  rw [List.append_assoc]
  exact List.take_left' len

/-- The extra store overwrites the carry destination rather than adding to it. -/
theorem nativeRow_carry (factor : BitVec 64) (right buffer : List (BitVec 64)) :
    (LimbMul.nativeRow factor right buffer)[right.length]?.getD 0 =
      BitVec.ofNat 64 (LimbMul.inner right.length factor right buffer 0).2 := by
  have len := LimbMul.inner_length right.length factor right buffer 0
  unfold LimbMul.nativeRow LimbMul.row
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [len, Nat.sub_self, List.singleton_append, List.getElem?_cons_zero,
    Option.getD_some]

/-- Earlier row processing leaves all words beyond this row's carry untouched. -/
theorem nativeRow_suffix (factor : BitVec 64) (right buffer : List (BitVec 64)) :
    (LimbMul.nativeRow factor right buffer).drop (right.length + 1) =
      buffer.drop (right.length + 1) := by
  have len := LimbMul.row_length factor right buffer
  unfold LimbMul.nativeRow
  exact List.drop_left' len

/-- Peeling the finalized low word exposes precisely the next native row state. -/
theorem nativeRows_cons (factor : BitVec 64) (left right buffer : List (BitVec 64)) :
    LimbMul.nativeRows (factor :: left) right buffer =
      (LimbMul.nativeRow factor right buffer).head?.getD 0 ::
        LimbMul.nativeRows left right (LimbMul.nativeRow factor right buffer).tail := rfl

/-- Current prefix/unread replacement in the exact inner-loop recurrence. -/
theorem inner_succ (remaining : Nat) (factor word old : BitVec 64)
    (right buffer : List (BitVec 64)) (carry : Nat) :
    LimbMul.inner (remaining + 1) factor (word :: right) (old :: buffer) carry =
      let next := LimbMul.step factor word old carry
      let rest := LimbMul.inner remaining factor right buffer next.2
      (next.1 :: rest.1, rest.2) := rfl

end SszArm.NatMul
