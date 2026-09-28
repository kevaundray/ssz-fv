import SszArm.BitVectorRoundOwned
import SszArm.NatAddZeroOwned

namespace SszArm.BitVector

open SszNative (NatOperand)
open SszNative.NatArithmetic
open Delimited (Protected)

private theorem committed_owned (writes : List Delimited.Span)
    (reservation : SszNative.Arena.Reservation) (words : List (BitVec 64)) (result : NatOperand)
    (success : (committed reservation words).result = .ok result)
    (buffer : NatAdd.OperandOwned writes (.large (BitVec.ofNat 64 reservation.pointer) words)) :
    NatAdd.OperandOwned writes result := by
  cases success
  exact NatAdd.fromWords_owned writes _ words buffer

private theorem wide_owned (writes : List Delimited.Span) (base capacity used : Nat)
    (wide : BitVec 128) (result : NatOperand)
    (success : (fromWide base capacity used wide).result = .ok result)
    (allocated : ∀ reservation, (fromWide base capacity used wide).allocation = some reservation →
      NatAdd.OperandOwned writes (.large (BitVec.ofNat 64 reservation.pointer)
        (fromWide base capacity used wide).written)) : NatAdd.OperandOwned writes result := by
  by_cases fits : wide.toNat < 2^64
  · simp only [fromWide, fits, ↓reduceIte] at success
    cases success
    trivial
  · cases reserved : SszNative.Arena.reserve base capacity used 2 with
    | none =>
      simp only [fromWide, fits, ↓reduceIte, reserved] at success
      cases success
    | some reservation =>
      simp only [fromWide, fits, ↓reduceIte, reserved] at success allocated
      exact committed_owned writes reservation _ result success (allocated reservation rfl)

private theorem add_owned (writes : List Delimited.Span) (left right : NatOperand)
    (base capacity used : Nat) (result : NatOperand)
    (leftOwned : NatAdd.OperandOwned writes left) (rightOwned : NatAdd.OperandOwned writes right)
    (allocated : ∀ reservation,
      (SszNative.NatAdd.run left right base capacity used).allocation = some reservation →
      NatAdd.OperandOwned writes (.large (BitVec.ofNat 64 reservation.pointer)
        (SszNative.NatAdd.run left right base capacity used).written))
    (success : (SszNative.NatAdd.run left right base capacity used).result = .ok result) :
    NatAdd.OperandOwned writes result := by
  by_cases hl : left.wordCount = 0
  · rw [SszNative.NatAdd.run_zero_left left right base capacity used hl] at success
    cases success
    exact NatAdd.normalized_owned writes right rightOwned
  · by_cases hr : right.wordCount = 0
    · rw [SszNative.NatAdd.run_zero_right left right base capacity used hl hr] at success
      cases success
      exact NatAdd.normalized_owned writes left leftOwned
    · by_cases small : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1
      · rw [SszNative.NatAdd.run_one_word left right base capacity used hl hr small] at success allocated
        exact wide_owned writes base capacity used _ result success allocated
      · rw [SszNative.NatAdd.run_large left right base capacity used hl hr small] at success allocated
        by_cases fits : SszNative.NatAdd.count left right + 1 < 2^64
        · simp only [fits, ↓reduceIte] at success allocated
          cases reserved : SszNative.Arena.reserve base capacity used (SszNative.NatAdd.count left right + 1) with
          | none =>
            rw [reserved] at success
            cases success
          | some reservation =>
            rw [reserved] at success allocated
            exact committed_owned writes reservation _ result success (allocated reservation rfl)
        · simp only [fits, ↓reduceIte] at success
          cases success

/-- A successful optional increment either normalizes an existing protected
operand or owns the prefix of its full freshly written buffer. -/
theorem rounded_local_owned {s : ArmState} {length quotient expected : NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (owned : Owned s length data)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0) (success : (rounding s length quotient).result = .ok expected) :
    NatDivision.OperandOwned (localWrites s) expected := by
  apply add_owned (localWrites s) quotient (.small 1) (arenaOf s).base (arenaOf s).capacity
    (SszNative.NatDivision.run length 8 (arenaOf s).base (arenaOf s).capacity (arenaOf s).used).used expected
    (quotient_local_owned owned division) (by trivial) ?_ success
  intro reservation allocated
  have geometry := SszNative.NatAdd.allocation_geometry quotient (.small 1) (arenaOf s).base
    (arenaOf s).capacity
    (SszNative.NatDivision.run length 8 (arenaOf s).base (arenaOf s).capacity (arenaOf s).used).used
    reservation allocated
  have extent : reservation.pointer + 8 * (rounding s length quotient).written.length =
      (arenaOf s).base + (rounding s length quotient).used := by
    dsimp only [rounding]
    rw [geometry.2.1, geometry.2.2.1]
    simp only [SszNative.Arena.finish, Nat.add_assoc]
  have positive : 0 < (rounding s length quotient).written.length := by
    dsimp only [rounding]
    have size := geometry.2.2.2
    split at size <;> omega
  have cursor := (rounded_cursor_bounds s length quotient data owned).2
  have storage := owned.arenaStorage
  have pointerBound : reservation.pointer < 2^64 := by omega
  have fresh := owned.fresh _ (rounded_write s length quotient remainder data division nonzero reservation allocated)
  have cover : Covers (localWrites s ++
      [((r (.GPR 31#5) s).toNat + 272, 96), ((r (.GPR 19#5) s).toNat, 24)]) (localWrites s) :=
    fun span member => ⟨span, List.mem_append_left _ member, Nat.le_refl _, Nat.le_refl _⟩
  change Protected (localWrites s) (BitVec.ofNat 64 reservation.pointer).toNat _
  simpa only [rounding, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound] using cover.protected fresh

end SszArm.BitVector
