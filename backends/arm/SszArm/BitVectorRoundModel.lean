import SszArm.BitVectorResources

namespace SszArm.BitVector

/-- The optional second helper starts at the division's committed cursor. -/
def rounding (s : ArmState) (length quotient : SszNative.NatOperand) :=
  SszNative.NatAdd.run quotient (.small 1) (arenaOf s).base (arenaOf s).capacity
    (SszNative.NatDivision.run length 8 (arenaOf s).base (arenaOf s).capacity (arenaOf s).used).used

theorem rounded_eq (s : ArmState) (length quotient : SszNative.NatOperand)
    (remainder : BitVec 64) (data : Ssz.Bytes)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0) :
    (outcome s length data).rounded = some (rounding s length quotient) := by
  cases result : (rounding s length quotient).result
  all_goals
    unfold rounding at result
    simp only [outcome, SszNative.BitVector.run, division, nonzero, ↓reduceIte,
      rounding, result]

theorem rounded_write (s : ArmState) (length quotient : SszNative.NatOperand)
    (remainder : BitVec 64) (data : Ssz.Bytes)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0) (reservation : SszNative.Arena.Reservation)
    (allocated : (rounding s length quotient).allocation = some reservation) :
    (reservation.pointer, 8 * (rounding s length quotient).written.length) ∈
      (outcome s length data).writes := by
  change _ ∈ SszNative.BitVector.allocationWrites (outcome s length data).divided ++ _
  apply List.mem_append_right
  rw [rounded_eq s length quotient remainder data division nonzero]
  simp only [SszNative.BitVector.allocationWrites, allocated, List.mem_singleton]

/-- Both allocations are charged on every later branch, including scope and
padding errors. No proof may silently reset the cursor to its entry value. -/
theorem rounded_cursor_bounds (s : ArmState) (length quotient : SszNative.NatOperand)
    (data : Ssz.Bytes) (owned : Owned s length data) :
    (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).used ≤ (rounding s length quotient).used ∧
      (rounding s length quotient).used ≤ (arenaOf s).capacity := by
  have divided := division_cursor_bounds s length data owned
  rw [outcome, divided_eq] at divided
  unfold rounding
  cases allocated : (rounding s length quotient).allocation with
  | none =>
    have resources := SszNative.NatAdd.no_allocation_resources quotient (.small 1)
      (arenaOf s).base (arenaOf s).capacity
      (SszNative.NatDivision.run length 8 (arenaOf s).base (arenaOf s).capacity (arenaOf s).used).used
      allocated
    exact ⟨by rw [resources.1]; exact Nat.le_refl _, by rw [resources.1]; exact divided.2⟩
  | some reservation =>
    have geometry := SszNative.NatAdd.allocation_geometry quotient (.small 1)
      (arenaOf s).base (arenaOf s).capacity
      (SszNative.NatDivision.run length 8 (arenaOf s).base (arenaOf s).capacity (arenaOf s).used).used
      reservation allocated
    have start := SszNative.Arena.used_le_start (arenaOf s).base
      (SszNative.NatDivision.run length 8 (arenaOf s).base (arenaOf s).capacity (arenaOf s).used).used
    rw [geometry.2.2.1]
    exact ⟨by unfold SszNative.Arena.finish; omega, geometry.1.2.2.2.2.2⟩

end SszArm.BitVector
