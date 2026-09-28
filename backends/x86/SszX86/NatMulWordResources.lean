import SszX86.NatMulWordOwnership
import SszX86.DelimitedReservation

namespace SszX86.NatMulWord
open SszNative UintCodec

theorem allocation_bounds (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation =
      some r) :
    0 < r.pointer ∧ r.pointer % 8 = 0 ∧
      address.toNat + used.toNat ≤ r.pointer ∧
      r.pointer + 8 * (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length =
        address.toNat + r.used ∧
      r.used ≤ capacity.toNat ∧
      r.pointer + 8 * (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length ≤
        2^64 := by
  obtain ⟨same, positive, reserved⟩ :=
    SszNative.NatMul.runWord_allocation_exact operand factor address.toNat capacity.toNat used.toNat r allocated
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
  dsimp only
  refine ⟨by omega, ?_, by omega, ?_, fits, ?_⟩
  · rw [Arena.start_pointer]
    exact Arena.aligned_mod _
  · simp only [Arena.finish, Nat.add_assoc]
  · unfold Arena.finish at fits
    omega

theorem allocated_pointer_nat (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation =
      some r) : (BitVec.ofNat 64 r.pointer).toNat = r.pointer := by
  have bounds := allocation_bounds s operand factor address capacity used ra owned r allocated
  have positive := (SszNative.NatMul.runWord_allocation_exact operand factor address.toNat capacity.toNat
    used.toNat r allocated).2.1
  exact Nat.mod_eq_of_lt (by omega)

/-- The complete written span is obtained from the original writable suffix.
This proves mapping after an actual reserve decision rather than assuming it. -/
theorem allocated_mapped (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (m : DataMem) (hm : Large.Mapped m (address + used) (capacity.toNat - used.toNat))
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation =
      some r) :
    Large.Mapped m (BitVec.ofNat 64 r.pointer)
      (8 * (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length) := by
  have bounds := allocation_bounds s operand factor address capacity used ra owned r allocated
  have hmSub := Delimited.Reservation.mapped_subrange m (address + used)
    (capacity.toNat - used.toNat) (r.pointer - (address.toNat + used.toNat))
    (8 * (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length)
    hm (by omega)
  have pointer : address + used + BitVec.ofNat 64 (r.pointer-(address.toNat+used.toNat)) =
      BitVec.ofNat 64 r.pointer := by bv_omega
  rw [pointer] at hmSub
  exact hmSub

theorem allocation_cursor (operand : NatOperand) (factor address capacity used : BitVec 64)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation =
      some r) :
    (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).used = r.used := by
  have same := (SszNative.NatMul.runWord_allocation_exact operand factor address.toNat capacity.toNat used.toNat
    r allocated).1
  exact congrArg NatArithmetic.Outcome.used same

theorem allocation_result (operand : NatOperand) (factor address capacity used : BitVec 64)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation =
      some r) :
    (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).result =
      .ok (NatOperand.fromWords (BitVec.ofNat 64 r.pointer)
        (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written) := by
  have same := (SszNative.NatMul.runWord_allocation_exact operand factor address.toNat capacity.toNat used.toNat
    r allocated).1
  exact congrArg NatArithmetic.Outcome.result same

end SszX86.NatMulWord
