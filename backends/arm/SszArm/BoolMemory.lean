import SszArm.BoolExec

namespace SszArm.BoolCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private theorem append_nat {n k : Nat} (x : BitVec n) (y : BitVec k) :
    (x ++ y).toNat = 2^k * x.toNat + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt x.toNat,
    Nat.shiftLeft_eq, Nat.mul_comm]

private theorem read_nat_succ (s : ArmState) (n : Nat) (address : BitVec 64) :
    (read_mem_bytes (n + 1) address s).toNat =
      256 * (read_mem_bytes n (address + 1#64) s).toNat + (read_mem address s).toNat := by
  rw [read_mem_bytes, BitVec.toNat_cast]
  exact append_nat (read_mem_bytes n (address + 1#64) s) (read_mem address s)

private theorem read_nat_zero (s : ArmState) (address : BitVec 64) :
    (read_mem_bytes 0 address s).toNat = 0 := rfl

/-- The two architectural LDP lanes are consecutive little-endian words. -/
theorem pair_read (s : ArmState) (address : BitVec 64) :
    read_mem_bytes 16 address s =
      read_mem_bytes 8 (address + 8#64) s ++ read_mem_bytes 8 address s := by
  apply BitVec.eq_of_toNat_eq
  rw [append_nat (read_mem_bytes 8 (address + 8#64) s) (read_mem_bytes 8 address s)]
  simp only [read_nat_succ, read_nat_zero]
  simp [BitVec.add_assoc]
  omega

theorem pair_read_low (s : ArmState) (address : BitVec 64) :
    (read_mem_bytes 16 address s).extractLsb' 0 64 = read_mem_bytes 8 address s := by
  rw [pair_read]
  exact BitVec.extractLsb'_append_right _ _

theorem pair_read_high (s : ArmState) (address : BitVec 64) :
    (read_mem_bytes 16 address s).extractLsb' 64 64 =
      read_mem_bytes 8 (address + 8#64) s := by
  rw [pair_read]
  exact BitVec.extractLsb'_append_left _ _

theorem read_one (s : ArmState) (address : BitVec 64) :
    read_mem_bytes 1 address s = read_mem address s := by
  simp only [read_mem_bytes]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cast, append_nat (0#0) (read_mem address s)]
  simp

theorem read_two (s : ArmState) (address : BitVec 64) :
    read_mem_bytes 2 address s =
      read_mem_bytes 1 (address + 1#64) s ++ read_mem_bytes 1 address s := by
  change (read_mem_bytes 1 (address + 1#64) s ++ read_mem address s).cast (by decide) = _
  simp only [read_one]
  rfl

end SszArm.BoolCodec
