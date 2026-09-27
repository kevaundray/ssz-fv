import SszX86.NatAddCarryMath

namespace SszX86.NatAdd.Carry
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Physical output extent bounds this mask; no signed capacity hypothesis is used. -/
theorem even_mask (count : Nat) (bound : count < 2^61) :
    2305843009213693950#64 &&& BitVec.ofNat 64 count =
      BitVec.ofNat 64 (2*(count/2)) := by
  have half : count / 2 < 2^60 := by omega
  have quotient : (count &&& 2305843009213693950) / 2 = count / 2 := by
    rw [Nat.and_div_two]
    change count / 2 &&& (2^60-1) = count / 2
    exact Nat.and_two_pow_sub_one_of_lt_two_pow half
  have residue : (count &&& 2305843009213693950) % 2 = 0 := by
    rw [show (2 : Nat) = 2^1 by rfl, Nat.and_mod_two_pow]
    simp
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show count < 2^64 by omega)]
  rw [show (2305843009213693950 : Nat) % 2^64 = 2305843009213693950 by decide]
  rw [Nat.and_comm]
  have reduced : 2*(count/2) < 2^64 := by omega
  rw [Nat.mod_eq_of_lt reduced]
  omega

/-- The AL parity test observes mathematical parity even at arbitrary count. -/
theorem parity_test (count : Nat) :
    ((BitVec.ofNat 64 count).extractLsb' 0 8 &&& 1#8 = 0#8) ↔ count % 2 = 0 := by
  have value :
      ((BitVec.ofNat 64 count).extractLsb' 0 8 &&& 1#8).toNat = count % 2 := by
    simp only [BitVec.toNat_and, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
      Nat.shiftRight_zero]
    change (count % 2^64 % 2^8 &&& 1) = count % 2
    rw [Nat.and_one_is_mod]
    omega
  constructor
  · intro h
    have eq := congrArg BitVec.toNat h
    rw [value] at eq
    exact eq
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [value, h]
    rfl

/-- Two machine writes consume two indexed native carry steps. -/
theorem pair_recurrence (remaining index : Nat) (left right : List (BitVec 64))
    (carry : Nat) :
    (LimbAdd.loop (remaining+2) (left.drop index) (right.drop index) carry).1 =
      let first := LimbAdd.step (limbAt left index) (limbAt right index) carry
      let second := LimbAdd.step (limbAt left (index+1)) (limbAt right (index+1)) first.2
      first.1 :: second.1 ::
        (LimbAdd.loop remaining (left.drop (index+2)) (right.drop (index+2)) second.2).1 := by
  rw [show remaining+2 = (remaining+1)+1 by omega]
  simp only [LimbAdd.loop_indexed_succ]

end SszX86.NatAdd.Carry
