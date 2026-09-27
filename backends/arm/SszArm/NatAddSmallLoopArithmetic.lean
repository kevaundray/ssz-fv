import SszArm.NatAddBlocks
import SszLimbAdd

namespace SszArm.NatAdd.SmallLoop

open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- After the first word the Small operand is exhausted. The actual ADDS at
+1912 therefore adds just the incoming carry and the original right word. -/
theorem add_low (word : BitVec 64) (carry : Nat) (hc : carry ≤ 1) :
    BitVec.ofNat 64 carry + word = (LimbAdd.step 0#64 word carry).1 := by
  apply BitVec.eq_of_toNat_eq
  have hcarry : carry < 2^64 := by omega
  simp [LimbAdd.step, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hcarry, Nat.add_comm]

/-- The machine C flag and the native outgoing carry coincide. -/
theorem add_carry (word : BitVec 64) (carry : Nat) (hc : carry ≤ 1) :
    (if (AddWithCarry (BitVec.ofNat 64 carry) word 0#1).2.c = 1#1
      then 1 else 0) = (LimbAdd.step 0#64 word carry).2 := by
  have hw := word.isLt
  have hcarry : carry < 2^64 := by omega
  have hflag : (AddWithCarry (BitVec.ofNat 64 carry) word 0#1).2.c = 1#1 ↔
      2^64 ≤ carry + word.toNat := by
    simpa [Udivti3.radix, Nat.mod_eq_of_lt hcarry] using
      Udivti3.adc_carry (BitVec.ofNat 64 carry) word 0#1
  simp only [LimbAdd.step, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add]
  simp only [hflag]
  split <;> omega

/-- The suffix recurrence uses the original untrimmed physical right list. -/
theorem suffix_succ (remaining index carry : Nat) (right : List (BitVec 64)) :
    LimbAdd.loop (remaining + 1) [] (right.drop index) carry =
      let next := LimbAdd.step 0#64 (right[index]?.getD 0#64) carry
      let rest := LimbAdd.loop remaining [] (right.drop (index + 1)) next.2
      (next.1 :: rest.1, rest.2) := by
  simpa using LimbAdd.loop_indexed_succ remaining index [] right carry

/-- A physical count is compared unsigned, including counts beyond isize. -/
theorem right_guard (index : Nat) (right : List (BitVec 64))
    (hi : index < 2^64) (hr : right.length < 2^64) :
    ((AddWithCarry (BitVec.ofNat 64 index)
      (~~~BitVec.ofNat 64 right.length) 1#1).2.c ≠ 1#1) ↔ index < right.length := by
  rw [ne_eq, Udivti3.cmp_carry]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hr]
  omega

/-- The final SUBS/B.EQ observes the remaining allocation, not input length. -/
theorem last_guard (remaining : Nat) (hr : remaining + 1 < 2^64) :
    (AddWithCarry (BitVec.ofNat 64 (remaining + 1)) (~~~(1#64)) 1#1).2.z = 1#1 ↔
      remaining = 0 := by
  rw [Udivti3.cmp_zero]
  bv_omega

end SszArm.NatAdd.SmallLoop
