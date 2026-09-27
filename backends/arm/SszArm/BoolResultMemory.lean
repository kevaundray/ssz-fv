import SszArm.BoolMemory
import SszBool

namespace SszArm.BoolCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Stores preserve every byte outside the written interval. -/
@[simp] theorem write_mem_bytes_frame (s : ArmState) (addr : BitVec 64)
    (width : Nat) (value : BitVec (width * 8)) (a : BitVec 64)
    (hspace : addr.toNat + width ≤ 2 ^ 64)
    (ha : a.toNat < addr.toNat ∨ addr.toNat + width ≤ a.toNat) :
    (write_mem_bytes width addr value s).mem a = s.mem a := by
  rw [Memory.write_mem_bytes_eq_mem_write_bytes]
  change s.mem.write_bytes width addr value a = s.mem a
  rcases ha with hbefore | hafter
  · exact Memory.write_bytes_eq_of_le hbefore hspace
  · exact Memory.write_bytes_eq_of_ge hafter hspace

/-- Read-after-write on the exact same interval. -/
@[simp] theorem read_mem_bytes_write_mem_bytes_same (s : ArmState) (n : Nat)
    (addr : BitVec 64) (value : BitVec (n * 8)) (hspace : addr.toNat + n ≤ 2 ^ 64) :
    read_mem_bytes n addr (write_mem_bytes n addr value s) = value := by
  rw [Memory.State.read_mem_bytes_eq_mem_read_bytes,
    Memory.write_mem_bytes_eq_mem_write_bytes]
  apply BitVec.eq_of_extractLsByte_eq
  intro i
  by_cases hi : i < n
  · rw [Memory.extractLsByte_read_bytes hspace, if_pos hi]
    change s.mem.write_bytes n addr value (addr + BitVec.ofNat 64 i) = _
    have hsub : (addr + BitVec.ofNat 64 i - addr).toNat = i := by bv_omega
    rw [Memory.write_bytes_eq_extractLsByte (by bv_omega) (by bv_omega) hspace, hsub]
  · rw [BitVec.extractLsByte_ge (by omega), BitVec.extractLsByte_ge (by omega)]

/-- A read interval disjoint from a write interval is unchanged. -/
@[simp] theorem read_mem_bytes_write_mem_bytes_disjoint (s : ArmState)
    (loadWidth storeWidth : Nat) (loadAddr storeAddr : BitVec 64)
    (value : BitVec (storeWidth * 8))
    (hload : loadAddr.toNat + loadWidth ≤ 2 ^ 64)
    (hstore : storeAddr.toNat + storeWidth ≤ 2 ^ 64)
    (hdisj : loadAddr.toNat + loadWidth ≤ storeAddr.toNat ∨
      storeAddr.toNat + storeWidth ≤ loadAddr.toNat) :
    read_mem_bytes loadWidth loadAddr (write_mem_bytes storeWidth storeAddr value s) =
      read_mem_bytes loadWidth loadAddr s := by
  rw [Memory.State.read_mem_bytes_eq_mem_read_bytes,
    Memory.write_mem_bytes_eq_mem_write_bytes,
    Memory.State.read_mem_bytes_eq_mem_read_bytes]
  apply BitVec.eq_of_extractLsByte_eq
  intro i
  by_cases hi : i < loadWidth
  · rw [Memory.extractLsByte_read_bytes hload, if_pos hi,
      Memory.extractLsByte_read_bytes hload, if_pos hi]
    change s.mem.write_bytes storeWidth storeAddr value (loadAddr + BitVec.ofNat 64 i) = _
    have haddr : (loadAddr + BitVec.ofNat 64 i).toNat = loadAddr.toNat + i := by bv_omega
    rcases hdisj with hbefore | hafter
    · rw [Memory.write_bytes_eq_of_le (by omega) hstore]
      rfl
    · rw [Memory.write_bytes_eq_of_ge (by omega) hstore]
      rfl
  · rw [BitVec.extractLsByte_ge (by omega), BitVec.extractLsByte_ge (by omega)]

/-- Logical scope-error image; lowering scratch traffic is handled separately. -/
def scopeMemory (s : ArmState) (out length : BitVec 64) : ArmState :=
  let s := write_mem_bytes 8 (out + 56#64) 0#64 s
  let s := write_mem_bytes 8 (out + 64#64) 0#64 s
  let s := write_mem_bytes 8 (out + 16#64) 0#64 s
  let s := write_mem_bytes 8 (out + 24#64) 0#64 s
  let s := write_mem_bytes 8 (out + 32#64) 1#64 s
  let s := write_mem_bytes 8 (out + 40#64) 0#64 s
  let s := write_mem_bytes 8 (out + 48#64) length s
  let s := write_mem_bytes 4 (out + 72#64) 3#32 s
  let s := write_mem_bytes 8 (out + 0#64) 1#64 s
  write_mem_bytes 8 (out + 8#64) 1#64 s

/-- Store order matches the invalid-byte path, including its shared error tail. -/
def badMemory (s : ArmState) (out byte : BitVec 64) : ArmState :=
  let s := write_mem_bytes 8 (out + 56#64) 0#64 s
  let s := write_mem_bytes 8 (out + 64#64) 0#64 s
  let s := write_mem_bytes 8 (out + 40#64) 0#64 s
  let s := write_mem_bytes 8 (out + 48#64) 0#64 s
  let s := write_mem_bytes 8 (out + 16#64) 0#64 s
  let s := write_mem_bytes 8 (out + 24#64) 0#64 s
  let s := write_mem_bytes 8 (out + 32#64) byte s
  let s := write_mem_bytes 4 (out + 72#64) 13#32 s
  let s := write_mem_bytes 8 (out + 0#64) 1#64 s
  write_mem_bytes 8 (out + 8#64) 1#64 s

/-- Store order matches the success path: payload first, then the tag. -/
def successMemory (s : ArmState) (out : BitVec 64) (value : Bool) : ArmState :=
  let s := write_mem_bytes 2 (out + 16#64) (if value then 256#16 else 0#16) s
  write_mem_bytes 8 (out + 0#64) 0#64 s

theorem write_pair_ones (s : ArmState) (out : BitVec 64) :
    write_mem_bytes 16 out 18446744073709551617#128 s =
      write_mem_bytes 8 (out + 8#64) 1#64 (write_mem_bytes 8 out 1#64 s) := by
  simp [write_mem_bytes, BitVec.add_assoc]

theorem write_bool_bytes (s : ArmState) (out : BitVec 64) (value : Bool) :
    write_mem_bytes 1 (out + 1#64) (if value then 1#8 else 0#8)
      (write_mem_bytes 1 out 0#8 s) =
        write_mem_bytes 2 out (if value then 256#16 else 0#16) s := by
  cases value <;> simp [write_mem_bytes, BitVec.add_assoc]

/-- The scope-error result image refines the native boolean decoder contract. -/
theorem scope_result (s : ArmState) (out length : BitVec 64)
    (hspace : out.toNat + 80 ≤ 2 ^ 64) :
    SszNative.BoolCodec.ResultAt
      (fun offset width => some (read_mem_bytes width
        (out + BitVec.ofNat 64 offset) (scopeMemory s out length)).toNat)
      (.error (.scope 1 length.toNat)) := by
  simp (disch := first | assumption | omega | decide | bv_omega)
    [scopeMemory, SszNative.BoolCodec.ResultAt, SszNative.BoolCodec.errorAt,
      SszNative.NatMemory.smallAt]

/-- The invalid-byte result image refines the native boolean decoder contract. -/
theorem bad_result (s : ArmState) (out byte : BitVec 64)
    (hspace : out.toNat + 80 ≤ 2 ^ 64) :
    SszNative.BoolCodec.ResultAt
      (fun offset width => some (read_mem_bytes width
        (out + BitVec.ofNat 64 offset) (badMemory s out byte)).toNat)
      (.error (.notABit byte.toNat)) := by
  simp (disch := first | assumption | omega | decide | bv_omega)
    [badMemory, SszNative.BoolCodec.ResultAt, SszNative.BoolCodec.errorAt,
      SszNative.NatMemory.smallAt]

/-- The success result image refines the native boolean decoder contract. -/
theorem success_result (s : ArmState) (out : BitVec 64) (value : Bool)
    (hspace : out.toNat + 80 ≤ 2 ^ 64) :
    SszNative.BoolCodec.ResultAt
      (fun offset width => some (read_mem_bytes width
        (out + BitVec.ofNat 64 offset) (successMemory s out value)).toNat)
      (.ok (.bool value)) := by
  cases value <;>
    simp (disch := first | assumption | omega | decide | bv_omega)
      [successMemory, SszNative.BoolCodec.ResultAt]

/-- Scope-error writes do not disturb bytes outside the 76-byte result region. -/
theorem scope_frame (s : ArmState) (out length : BitVec 64) (a : BitVec 64)
    (hspace : out.toNat + 80 ≤ 2 ^ 64)
    (ha : a.toNat < out.toNat ∨ out.toNat + 76 ≤ a.toNat) :
    (scopeMemory s out length).mem a = s.mem a := by
  simp (disch := first | assumption | omega | decide | bv_omega) [scopeMemory]

/-- Invalid-byte writes do not disturb bytes outside the 76-byte result region. -/
theorem bad_frame (s : ArmState) (out byte : BitVec 64) (a : BitVec 64)
    (hspace : out.toNat + 80 ≤ 2 ^ 64)
    (ha : a.toNat < out.toNat ∨ out.toNat + 76 ≤ a.toNat) :
    (badMemory s out byte).mem a = s.mem a := by
  simp (disch := first | assumption | omega | decide | bv_omega) [badMemory]

/-- Success writes do not disturb bytes outside the 18-byte result region. -/
theorem success_frame (s : ArmState) (out : BitVec 64) (value : Bool) (a : BitVec 64)
    (hspace : out.toNat + 80 ≤ 2 ^ 64)
    (ha : a.toNat < out.toNat ∨ out.toNat + 18 ≤ a.toNat) :
    (successMemory s out value).mem a = s.mem a := by
  simp (disch := first | assumption | omega | decide | bv_omega) [successMemory]

end SszArm.BoolCodec
