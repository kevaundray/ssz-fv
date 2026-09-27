import SszX86.MemsetImpl
import SszX86.MemcpyMemory

namespace SszX86

open Std.ExtHashMap

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The destination's current bytes and an unchanged caller-owned frame. -/
def FillMem (m : DataMem) (dst : BitVec 64)
    (bytes : List UInt8) (R : DataMem → Prop) : Prop :=
  m =⋆ Eq (bytes.At dst) ⋆ R

/-- Little-endian replication of a single byte across eight machine bytes. -/
def memsetBroadcast : Nat → Nat
| 0 => 0
| n + 1 => 1 + 256 * memsetBroadcast n

/-- The unsigned value of the low byte supplied to memset. -/
def memsetByteValue (b : UInt8) : Int :=
  Int.ofNat b.toNat

/-- The actual `movabsq; imulq` broadcast word for the fill byte. -/
def memsetFillValue (b : UInt8) : Int :=
  Int.ofNat (b.toNat * memsetBroadcast 8)

theorem memset_replicate_ofBytes (b : UInt8) :
    ∀ n, Int.ofBytes (List.replicate n b) = Int.ofNat (b.toNat * memsetBroadcast n)
| 0 => rfl
| n + 1 => by
    rw [List.replicate_succ, Int.ofBytes_cons, memset_replicate_ofBytes b n]
    simp [memsetBroadcast, Nat.mul_add, Int.mul_assoc, Int.mul_comm, Int.add_comm]

/-- The actual eight-byte broadcast word stores the repeated fill byte. -/
theorem memset_roundtrip (b : UInt8) :
    Int.toBytes 8 (memsetFillValue b) = List.replicate 8 b := by
  have h : memsetFillValue b = Int.ofBytes (List.replicate 8 b) := by
    simpa [memsetFillValue] using (memset_replicate_ofBytes b 8).symm
  simpa [h] using (Int.toBytes_ofBytes_all (List.replicate 8 b))

/-- A single-byte store of the low byte preserves the exact byte value. -/
theorem memset_byte_roundtrip (b : UInt8) :
    Int.toBytes 1 (memsetByteValue b) = [b] := by
  have h : memsetByteValue b = Int.ofBytes [b] := by
    simp [memsetByteValue, Int.ofBytes]
  simpa [h] using (Int.toBytes_ofBytes_all [b])

theorem memset_signed_roundtrip (b : UInt8) :
    Int.toBytes 8 (BitVec.ofInt 64 (memsetFillValue b)).toInt = List.replicate 8 b := by
  have h : memsetFillValue b = Int.ofBytes (List.replicate 8 b) :=
    (memset_replicate_ofBytes b 8).symm
  rw [h]
  exact memcpy_roundtrip 8 _ (by simp)

theorem memset_byte_signed_roundtrip (b : UInt8) :
    Int.toBytes 1 (BitVec.ofInt 8 (memsetByteValue b)).toInt = [b] := by
  have h : memsetByteValue b = Int.ofBytes [b] := by
    simp [memsetByteValue, Int.ofBytes]
  rw [h]
  exact memcpy_roundtrip 1 _ rfl

private theorem split_at (xs : List UInt8) (p : BitVec 64) (k : Nat)
    (hk : k ≤ xs.length) (hb : xs.length ≤ 2^64) :
    Eq (xs.At p) = Eq ((xs.take k).At p) ⋆
      Eq ((xs.drop k).At (p + BitVec.ofNat 64 k)) := by
  conv =>
    lhs
    rw [← List.take_append_drop k xs]
  rw [Mem.At_append_sep _ _ _ (by simp; omega)]
  rw [List.length_take_of_le hk]

/-- One mapped store advances over the destination and frames the filled prefix. -/
theorem memset_chunk (m : DataMem) (dst : BitVec 64)
    (old value : List UInt8) (R : DataMem → Prop) (k : Nat)
    (hv : value.length = k) (hk : k ≤ old.length) (hb : old.length ≤ 2^64)
    (hm : FillMem m dst old R) :
    Mem.loadInt m dst k = some (Int.ofBytes (old.take k)) ∧
    FillMem (Mem.storeBytes m dst value) (dst + BitVec.ofNat 64 k)
      (old.drop k) (Eq (value.At dst) ⋆ R) := by
  have hsplit : m =⋆ Eq ((old.take k).At dst) ⋆
      (Eq ((old.drop k).At (dst + BitVec.ofNat 64 k)) ⋆ R) := by
    dsimp [FillMem] at hm
    rwa [split_at old dst k hk hb, sep_assoc] at hm
  refine ⟨Mem.loadInt_sep _ dst k _ m hsplit (List.length_take_of_le hk) (by omega), ?_⟩
  have hs := Mem.storeBytes_sep dst k (old.take k) value
    (Eq ((old.drop k).At (dst + BitVec.ofNat 64 k)) ⋆ R) m
    ⟨hsplit, List.length_take_of_le hk, hv⟩
  dsimp [FillMem]
  rwa [sep_comm_l] at hs

/-- Recombine the filled prefix and suffix without changing the caller frame. -/
theorem memset_join (m : DataMem) (dst : BitVec 64)
    (xs : List UInt8) (R : DataMem → Prop) (k : Nat)
    (hk : k ≤ xs.length) (hb : xs.length ≤ 2^64)
    (hm : FillMem m (dst + BitVec.ofNat 64 k) (xs.drop k)
      (Eq ((xs.take k).At dst) ⋆ R)) :
    FillMem m dst xs R := by
  dsimp [FillMem] at *
  rw [split_at xs dst k hk hb]
  rw [sep_assoc, sep_comm_l]
  exact hm

/-- An exact frame identifies every byte in the resulting memory. -/
theorem memset_memory_unique (m : DataMem) (dst : BitVec 64)
    (bytes : List UInt8) (frame : DataMem)
    (hm : FillMem m dst bytes (Eq frame)) :
    m = (bytes.At dst).union frame := by
  rcases hm with ⟨_, _, h_union, _, rfl, rfl⟩
  exact h_union.symm

end SszX86
