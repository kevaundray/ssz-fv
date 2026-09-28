import SszArm.SerializeFinishReturn
import SszArm.UintResultMemory

namespace SszArm.Serialize.Finish

open Delimited (MemoryFrame)

/-- Rewriting original bytes cannot enlarge a frame, even inside the written interval. -/
theorem observed_store_frame (s t : ArmState) (writes : List (Nat × Nat))
    (frame : MemoryFrame writes s t) (address : BitVec 64) (bytes : Nat)
    (bound : address.toNat + bytes ≤ 2^64) :
    MemoryFrame writes s (write_mem_bytes bytes address (read_mem_bytes bytes address s) t) := by
  intro a outside
  by_cases before : a.toNat < address.toNat
  · rw [BoolCodec.write_mem_bytes_frame _ _ _ _ _ bound (Or.inl before)]
    exact frame a outside
  by_cases after : address.toNat + bytes ≤ a.toNat
  · rw [BoolCodec.write_mem_bytes_frame _ _ _ _ _ bound (Or.inr after)]
    exact frame a outside
  rw [Memory.write_mem_bytes_eq_mem_write_bytes,
    Memory.State.read_mem_bytes_eq_mem_read_bytes]
  change t.mem.write_bytes bytes address (s.mem.read_bytes bytes address) a = s.mem a
  rw [Memory.write_bytes_eq_extractLsByte (by omega) (by omega) bound,
    Memory.extractLsByte_read_bytes bound, if_pos (by bv_omega)]
  congr 1
  bv_omega

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

/-- Consecutive 32-bit lanes, used by the final error-propagation STP. -/
theorem pair_read_dwords (s : ArmState) (address : BitVec 64) :
    read_mem_bytes 8 address s =
      read_mem_bytes 4 (address + 4#64) s ++ read_mem_bytes 4 address s := by
  apply BitVec.eq_of_toNat_eq
  rw [append_nat]
  simp only [read_nat_succ, read_nat_zero]
  simp [BitVec.add_assoc]
  omega

/-- Word equality gives byte equality without assuming either image was initialized. -/
theorem copied_word_byte (s t : ArmState) (source target : BitVec 64) (bytes index : Nat)
    (sourceBound : source.toNat + bytes ≤ 2^64)
    (targetBound : target.toNat + bytes ≤ 2^64) (within : index < bytes)
    (copied : read_mem_bytes bytes target t = read_mem_bytes bytes source s) :
    t.mem (target + BitVec.ofNat 64 index) = s.mem (source + BitVec.ofNat 64 index) := by
  have observation := congrArg (fun value : BitVec (bytes * 8) => value.extractLsByte index) copied
  simpa only [Memory.State.read_mem_bytes_eq_mem_read_bytes,
    Memory.extractLsByte_read_bytes targetBound,
    Memory.extractLsByte_read_bytes sourceBound, if_pos within, Memory.read, read_store] using observation

end SszArm.Serialize.Finish
