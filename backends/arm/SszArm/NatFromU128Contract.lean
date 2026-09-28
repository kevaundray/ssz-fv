import SszArm.NatFromU128Entry
import SszArm.NatFromU128Observe
import SszArm.NatToU128Finish
import SszNatAddMemory

namespace SszArm.NatFromU128

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

def wide (s : ArmState) : BitVec 128 := r (.GPR 3#5) s ++ r (.GPR 2#5) s

def outcome (s : ArmState) : SszNative.NatArithmetic.Outcome SszNative.NatOperand :=
  SszNative.NatArithmetic.fromWide (addressWord s).toNat (capacityWord s).toNat
    (usedWord s).toNat (wide s)

/-- Ownership concerns original storage only. Invalid cursors are allowed;
zero/free suffix length then makes the suffix obligation vacuous. -/
structure Owned (s : ArmState) extends Space s where
  header : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64
  storage : (addressWord s).toNat + (capacityWord s).toNat ≤ 2^64
  nonnull : 0 < (capacityWord s).toNat → 0 < (addressWord s).toNat
  headerLocal : Protected (localWrites s) (r (.GPR 4#5) s).toNat 24
  free : Protected (localWrites s ++ [((r (.GPR 4#5) s).toNat, 24)])
    ((addressWord s).toNat + (usedWord s).toNat)
    ((capacityWord s).toNat - (usedWord s).toNat)

def writesFor (s : ArmState) : List Span :=
  (match (outcome s).result with | .ok _ => successWrites s | .error _ => localWrites s) ++
    (match (outcome s).allocation with
    | none => []
    | some reservation => [((r (.GPR 4#5) s).toNat + 16, 8), (reservation.pointer, 16)])

structure Post (s t : ArmState) : Prop where
  returned : Returned s t
  result : SszNative.NatArithmetic.AddResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (outcome s).result
  cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat = (outcome s).used
  header : read_mem_bytes 8 (r (.GPR 4#5) s) t = addressWord s ∧
    read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) t = capacityWord s
  frame : MemoryFrame (writesFor s) s t
  written : ∀ reservation, (outcome s).allocation = some reservation →
    (SszNative.NatOperand.large (BitVec.ofNat 64 reservation.pointer)
      (outcome s).written).At (widthLoad t)

theorem wide_low (s : ArmState) : (wide s).setWidth 64 = r (.GPR 2#5) s := by
  apply BitVec.eq_of_toNat_eq
  exact NatToU128.append_low _ _

theorem wide_high (s : ArmState) : ((wide s) >>> (64 : Nat)).setWidth 64 = r (.GPR 3#5) s := by
  apply BitVec.eq_of_toNat_eq
  exact NatToU128.append_high _ _

theorem wide_small (s : ArmState) : (wide s).toNat < 2^64 ↔ r (.GPR 3#5) s = 0#64 := by
  rw [wide, NatToU128.append_toNat]
  have low := (r (.GPR 2#5) s).isLt
  have high := (r (.GPR 3#5) s).isLt
  constructor
  · intro fits
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  · intro zero
    simp only [zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.zero_add]
    exact low

theorem outcome_small (s : ArmState) (small : r (.GPR 3#5) s = 0#64) :
    outcome s = SszNative.NatArithmetic.unchanged (usedWord s).toNat
      (.ok (.small (r (.GPR 2#5) s))) := by
  simp only [outcome, SszNative.NatArithmetic.fromWide, (wide_small s).2 small,
    ↓reduceIte, wide_low]

theorem outcome_failure (s : ArmState) (large : r (.GPR 3#5) s ≠ 0#64)
    (failed : SszNative.Arena.reserve (addressWord s).toNat (capacityWord s).toNat
      (usedWord s).toNat 2 = none) :
    outcome s = SszNative.NatArithmetic.unchanged (usedWord s).toNat (.error .scratchExhausted) := by
  simp only [outcome, SszNative.NatArithmetic.fromWide,
    show ¬ (wide s).toNat < 2^64 from fun h => large ((wide_small s).1 h),
    ↓reduceIte, failed]

theorem outcome_wide (s : ArmState) (large : r (.GPR 3#5) s ≠ 0#64)
    (checks : SszNative.Arena.Checks (addressWord s).toNat (capacityWord s).toNat
      (usedWord s).toNat 2) :
    outcome s = ⟨.ok (.large
      (BitVec.ofNat 64 ((addressWord s).toNat + SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat))
      [r (.GPR 2#5) s, r (.GPR 3#5) s]),
      SszNative.Arena.finish (addressWord s).toNat (usedWord s).toNat 2,
      some ⟨(addressWord s).toNat + SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat,
        SszNative.Arena.finish (addressWord s).toNat (usedWord s).toNat 2⟩,
      [r (.GPR 2#5) s, r (.GPR 3#5) s]⟩ := by
  simp [outcome, SszNative.NatArithmetic.fromWide,
    show ¬ (wide s).toNat < 2^64 from fun h => large ((wide_small s).1 h),
    SszNative.Arena.reserve, checks, wide_low, wide_high,
    SszNative.NatArithmetic.committed, SszNative.NatOperand.fromWords,
    SszNative.Limbs.trim, large]

/-- Successful reservations are contained in the original physical free suffix.
This is derived from the actual guards and does not occur as an entry premise. -/
theorem Owned.wideSpace {s u : ArmState} (owned : Owned s)
    (reached : Checkpoint s u) (selected : Selected s u .wide) :
    WideSpace u ∧ (pointer u).toNat =
      (addressWord s).toNat + SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat := by
  rcases selected with ⟨large, checks, address, first, last⟩
  have start := SszNative.Arena.used_le_start (addressWord s).toNat (usedWord s).toNat
  have finish := checks.2.2.2.2.2
  have finishEq : SszNative.Arena.finish (addressWord s).toNat (usedWord s).toNat 2 =
      SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat + 16 := rfl
  have storage := owned.storage
  have positive := owned.nonnull (by omega)
  have pointerNat : (pointer u).toNat =
      (addressWord s).toNat + SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat := by
    simp only [pointer, BitVec.toNat_add, address, first]
    exact Nat.mod_eq_of_lt (by omega)
  have out := reached.frame.registers 0#5 (by decide)
  have hdr := reached.frame.registers 4#5 (by decide)
  have fresh : ∀ span ∈ localWrites s ++ [((r (.GPR 4#5) s).toNat, 24)],
      (pointer u).toNat + 16 ≤ span.1 ∨ span.1 + span.2 ≤ (pointer u).toNat := by
    intro span member
    rcases owned.free with empty | separate
    · omega
    · have apart := separate span member
      rw [pointerNat]
      omega
  have fo := fresh ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites])
  have fs := fresh ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [localWrites])
  have fh := fresh ((r (.GPR 4#5) s).toNat, 24) (by simp)
  have headerApart : ∀ span ∈ localWrites s,
      (r (.GPR 4#5) s).toNat + 24 ≤ span.1 ∨ span.1 + span.2 ≤ (r (.GPR 4#5) s).toNat := by
    rcases owned.headerLocal with empty | separate
    · contradiction
    · exact separate
  have ho := headerApart ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites])
  have hs := headerApart ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [localWrites])
  refine ⟨⟨reached.frame.space owned.toSpace, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, pointerNat⟩
  · simpa only [hdr] using owned.header
  · rw [pointerNat]; omega
  · rw [pointerNat, SszNative.Arena.start_pointer]
    exact SszNative.Arena.aligned_mod _
  · rw [pointerNat]; omega
  · simpa only [out] using fo
  · rw [reached.frame.sp]
    have stack := owned.stack
    omega
  · simpa only [hdr] using fh
  · simpa only [hdr, out] using ho
  · rw [hdr, reached.frame.sp]
    have stack := owned.stack
    omega

end SszArm.NatFromU128
