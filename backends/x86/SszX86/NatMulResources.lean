import SszX86.NatMulOwnership
import SszX86.DelimitedReservation

namespace SszX86.NatMul
open SszNative
open UintCodec

/-- Every committed model branch reserves its entire written buffer, including
high zero limbs later omitted from the returned representation. -/
theorem allocation_bounds (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation =
      some r) :
    0 < r.pointer ∧ r.pointer % 8 = 0 ∧
      address.toNat + used.toNat ≤ r.pointer ∧
      r.pointer + 8 * (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length =
        address.toNat + r.used ∧
      r.used ≤ capacity.toNat ∧
      r.pointer + 8 * (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length ≤
        2^64 := by
  obtain ⟨same, positive, reserved⟩ :=
    SszNative.NatMul.allocation_exact left right address.toNat capacity.toNat used.toNat r allocated
  obtain ⟨checks, geometry⟩ :=
    (Arena.reserve_eq_some_iff_checks _ _ _ _ positive r).mp reserved
  have cursor := Arena.used_le_start address.toNat used.toNat
  have storage := owned.arena_bound
  have fits := checks.2.2.2.2.2
  have capacityPositive : 0 < capacity.toNat := by
    unfold Arena.finish at fits
    omega
  have basePositive := owned.arena_nonzero capacityPositive
  rw [geometry]
  change 0 < address.toNat + Arena.start address.toNat used.toNat ∧
    (address.toNat + Arena.start address.toNat used.toNat) % 8 = 0 ∧
    address.toNat + used.toNat ≤ address.toNat + Arena.start address.toNat used.toNat ∧
    address.toNat + Arena.start address.toNat used.toNat +
        8 * (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length =
      address.toNat + Arena.finish address.toNat used.toNat
        (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length ∧
    Arena.finish address.toNat used.toNat
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length ≤ capacity.toNat ∧
    address.toNat + Arena.start address.toNat used.toNat +
      8 * (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length ≤ 2^64
  refine ⟨by omega, ?_, by omega, ?_, fits, ?_⟩
  · rw [Arena.start_pointer]
    exact Arena.aligned_mod _
  · simp only [Arena.finish, Nat.add_assoc]
  · unfold Arena.finish at fits
    omega

theorem allocation_cursor (left right : NatOperand) (address capacity used : BitVec 64)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation =
      some r) :
    (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).used = r.used := by
  have same := (SszNative.NatMul.allocation_exact left right address.toNat capacity.toNat used.toNat
    r allocated).1
  exact congrArg NatArithmetic.Outcome.used same

theorem allocated_pointer_nat (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation =
      some r) : (BitVec.ofNat 64 r.pointer).toNat = r.pointer := by
  have bounds := allocation_bounds s left right address capacity used ra owned r allocated
  have positive := (SszNative.NatMul.allocation_exact left right address.toNat capacity.toNat
    used.toNat r allocated).2.1
  exact Nat.mod_eq_of_lt (by omega)

theorem allocated_mapped (left right : NatOperand) (address capacity used : BitVec 64)
    (m : DataMem) (hm : Large.Mapped m (address + used) (capacity.toNat - used.toNat))
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation =
      some r) :
    Large.Mapped m (BitVec.ofNat 64 r.pointer)
      (8 * (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length) := by
  have geometry := SszNative.NatMul.allocation_geometry left right address.toNat capacity.toNat
    used.toNat r allocated
  have cursor := Arena.used_le_start address.toNat used.toNat
  have fits := geometry.1.2.2.2.2.2
  have hmSub := Delimited.Reservation.mapped_subrange m (address + used)
    (capacity.toNat - used.toNat) (Arena.start address.toNat used.toNat - used.toNat)
    (8 * (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length)
    hm (by unfold Arena.finish at fits; omega)
  have pointer : (address + used) +
      BitVec.ofNat 64 (Arena.start address.toNat used.toNat - used.toNat) =
      BitVec.ofNat 64 r.pointer := by
    have offset : used.toNat + (Arena.start address.toNat used.toNat - used.toNat) =
        Arena.start address.toNat used.toNat := by omega
    calc
      (address + used) + BitVec.ofNat 64 (Arena.start address.toNat used.toNat - used.toNat) =
          address + BitVec.ofNat 64 (used.toNat + (Arena.start address.toNat used.toNat - used.toNat)) := by
        simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]
      _ = BitVec.ofNat 64 r.pointer := by
        simp only [offset, geometry.2.1, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [pointer] at hmSub
  exact hmSub

/-- Successful reservation determines exactly the represented result and cursor;
normalization never refunds high zero limbs or alignment padding. -/
theorem allocation_result (left right : NatOperand) (address capacity used : BitVec 64)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation =
      some r) :
    (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result =
      .ok (NatOperand.fromWords (BitVec.ofNat 64 r.pointer)
        (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written) := by
  have same := (SszNative.NatMul.allocation_exact left right address.toNat capacity.toNat used.toNat
    r allocated).1
  exact congrArg NatArithmetic.Outcome.result same

/-- All error branches leave both the allocation and cursor unchanged. -/
theorem failure_resources (left right : NatOperand) (address capacity used : BitVec 64)
    (reason : NatArithmetic.Failure)
    (failed : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result =
      .error reason) :
    reason = .scratchExhausted ∧
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = none ∧
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written = [] ∧
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).used = used.toNat := by
  have unchanged := SszNative.NatMul.failure_unchanged left right address.toNat capacity.toNat
    used.toNat reason failed
  have valid := SszNative.NatMul.no_badRepresentation left right address.toNat capacity.toNat used.toNat
  have scratch : reason = .scratchExhausted := by
    cases reason with
    | scratchExhausted => rfl
    | badRepresentation => exact False.elim (valid failed)
  rw [unchanged]
  exact ⟨scratch, rfl, rfl, rfl⟩

end SszX86.NatMul
