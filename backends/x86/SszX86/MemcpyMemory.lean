import SszX86.MemcpyImpl
import SszX86.Bytes

namespace SszX86

open Std.ExtHashMap

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Both buffers and an arbitrary, unchanged caller-owned frame. -/
def CopyMem (m : DataMem) (src dst : BitVec 64)
    (xs old : List UInt8) (R : DataMem → Prop) : Prop :=
  m =⋆ Eq (old.At dst) ⋆ (Eq (xs.At src) ⋆ R)

/-- The signed register interpretation of a loaded chunk preserves every byte. -/
theorem memcpy_roundtrip (k : Nat) (xs : List UInt8) (hlen : xs.length = k) :
    Int.toBytes k (BitVec.ofInt (8 * k) (Int.ofBytes xs)).toInt = xs := by
  rw [BitVec.toInt_ofInt]
  rw [show 2 ^ (8 * k) = 256 ^ k by
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]]
  exact Int.toBytes_bmod_ofBytes k xs hlen

private theorem split_at (xs : List UInt8) (p : BitVec 64) (k : Nat)
    (hk : k ≤ xs.length) (hb : xs.length ≤ 2^64) :
    Eq (xs.At p) = Eq ((xs.take k).At p) ⋆
      Eq ((xs.drop k).At (p + BitVec.ofNat 64 k)) := by
  conv =>
    lhs
    rw [← List.take_append_drop k xs]
  rw [Mem.At_append_sep _ _ _ (by simp; omega)]
  rw [List.length_take_of_le hk]

/-- After one mapped load/store, the remaining buffers are owned separately
from both already copied prefixes. This is the loop's memory induction step. -/
theorem memcpy_chunk (m : DataMem) (src dst : BitVec 64)
    (xs old : List UInt8) (R : DataMem → Prop) (k : Nat)
    (hlen : old.length = xs.length) (hk : k ≤ xs.length)
    (hb : xs.length ≤ 2^64) (hm : CopyMem m src dst xs old R) :
    Mem.loadInt m src k = some (Int.ofBytes (xs.take k)) ∧
    Mem.loadInt m dst k = some (Int.ofBytes (old.take k)) ∧
    CopyMem (Mem.storeBytes m dst (xs.take k))
      (src + BitVec.ofNat 64 k) (dst + BitVec.ofNat 64 k)
      (xs.drop k) (old.drop k)
      (Eq ((xs.take k).At dst) ⋆ (Eq ((xs.take k).At src) ⋆ R)) := by
  have hx := split_at xs src k hk hb
  have ho := split_at old dst k (by omega) (by omega)
  let A := Eq ((old.take k).At dst)
  let B := Eq ((old.drop k).At (dst + BitVec.ofNat 64 k))
  let C := Eq ((xs.take k).At src)
  let D := Eq ((xs.drop k).At (src + BitVec.ofNat 64 k))
  have hsplit : m =⋆ A ⋆ (C ⋆ (B ⋆ (D ⋆ R))) := by
    dsimp [CopyMem] at hm
    rw [hx, ho] at hm
    change m =⋆ (A ⋆ B) ⋆ ((C ⋆ D) ⋆ R) at hm
    rwa [show (A ⋆ B) ⋆ ((C ⋆ D) ⋆ R) = A ⋆ (C ⋆ (B ⋆ (D ⋆ R))) by ac_rfl] at hm
  have hsrc : m =⋆ C ⋆ (A ⋆ (B ⋆ (D ⋆ R))) := by
    rwa [sep_comm_l] at hsplit
  refine ⟨Mem.loadInt_sep _ src k _ m hsrc (List.length_take_of_le hk) (by omega),
    Mem.loadInt_sep _ dst k _ m hsplit (List.length_take_of_le (by omega)) (by omega), ?_⟩
  have hs := Mem.storeBytes_sep dst k (old.take k) (xs.take k)
    (C ⋆ (B ⋆ (D ⋆ R))) m
    ⟨hsplit, List.length_take_of_le (by omega), List.length_take_of_le hk⟩
  dsimp [CopyMem]
  change Mem.storeBytes m dst (xs.take k) =⋆ B ⋆ (D ⋆ (Eq ((xs.take k).At dst) ⋆ (C ⋆ R)))
  rwa [show Eq ((xs.take k).At dst) ⋆ (C ⋆ (B ⋆ (D ⋆ R))) =
    B ⋆ (D ⋆ (Eq ((xs.take k).At dst) ⋆ (C ⋆ R))) by ac_rfl] at hs

/-- Recombine the unchanged source and newly copied destination after the
recursive call. This includes the caller frame, not just the copied bytes. -/
theorem memcpy_join (m : DataMem) (src dst : BitVec 64)
    (xs : List UInt8) (R : DataMem → Prop) (k : Nat)
    (hk : k ≤ xs.length) (hb : xs.length ≤ 2^64)
    (hm : CopyMem m (src + BitVec.ofNat 64 k) (dst + BitVec.ofNat 64 k)
      (xs.drop k) (xs.drop k)
      (Eq ((xs.take k).At dst) ⋆ (Eq ((xs.take k).At src) ⋆ R))) :
    CopyMem m src dst xs xs R := by
  dsimp [CopyMem] at *
  rw [split_at xs src k hk hb, split_at xs dst k hk hb]
  simpa only [sep_assoc, sep_comm, sep_comm_l] using hm

/-- An exact frame, unlike a mere property of a frame, identifies all memory. -/
theorem memcpy_memory_unique (m : DataMem) (src dst : BitVec 64)
    (xs old : List UInt8) (frame : DataMem)
    (hm : CopyMem m src dst xs old (Eq frame)) :
    m = (old.At dst).union ((xs.At src).union frame) := by
  rcases hm with ⟨a, b, hab, _, rfl, c, d, hcd, _, rfl, rfl⟩
  subst b
  exact hab.symm

end SszX86
