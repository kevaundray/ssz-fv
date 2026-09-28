import SszArena

set_option autoImplicit false

namespace SszNative.Arena

/-- `reserve::<MaybeUninit<u8>>`: alignment one has no padding. The isize
restriction is a physical allocation guard, not a bound on any SSZ natural. -/
def ByteChecks (base capacity used bytes : Nat) : Prop :=
  bytes < 2 ^ 63 ∧ base + used < 2 ^ 64 ∧ used < 2 ^ 64 ∧
    used + bytes < 2 ^ 64 ∧ used + bytes ≤ capacity

instance (base capacity used bytes : Nat) : Decidable (ByteChecks base capacity used bytes) := by
  unfold ByteChecks
  infer_instance

/-- Empty byte slices use dangling pointer one, unlike the word allocator's
pointer eight. The zero branch does not inspect or change arena metadata. -/
def reserveBytes (base capacity used bytes : Nat) : Option Reservation :=
  if bytes = 0 then some ⟨1, used⟩
  else if ByteChecks base capacity used bytes then some ⟨base + used, used + bytes⟩
  else none

@[simp] theorem reserveBytes_zero (base capacity used : Nat) :
    reserveBytes base capacity used 0 = some ⟨1, used⟩ := by
  simp [reserveBytes]

theorem reserveBytes_some_iff (base capacity used bytes : Nat) (positive : 0 < bytes)
    (reservation : Reservation) :
    reserveBytes base capacity used bytes = some reservation ↔
      ByteChecks base capacity used bytes ∧ reservation = ⟨base + used, used + bytes⟩ := by
  have nonzero : bytes ≠ 0 := by omega
  by_cases checks : ByteChecks base capacity used bytes <;>
    simp [reserveBytes, nonzero, checks, eq_comm]

theorem reserveBytes_none_iff (base capacity used bytes : Nat) :
    reserveBytes base capacity used bytes = none ↔
      bytes ≠ 0 ∧ ¬ ByteChecks base capacity used bytes := by
  by_cases zero : bytes = 0 <;> by_cases checks : ByteChecks base capacity used bytes <;>
    simp [reserveBytes, zero, checks]

/-- On valid storage the remaining-byte condition is exact; arbitrary logical
sizes are rejected here only when they cannot be represented as an allocation. -/
theorem byteChecks_iff_fits (base capacity used bytes : Nat)
    (valid : Valid base capacity used) (positive : 0 < bytes) :
    ByteChecks base capacity used bytes ↔
      bytes < 2 ^ 63 ∧ bytes ≤ capacity - used := by
  rcases valid with ⟨basePositive, capacityBound, addressBound, cursorBound⟩
  unfold ByteChecks
  omega

theorem reserveBytes_valid (base capacity used bytes : Nat)
    (valid : Valid base capacity used) (reservation : Reservation)
    (success : reserveBytes base capacity used bytes = some reservation) :
    Valid base capacity reservation.used := by
  by_cases zero : bytes = 0
  · subst bytes
    have same : (⟨1, used⟩ : Reservation) = reservation := by simpa using success
    subst reservation
    exact valid
  · obtain ⟨checks, same⟩ :=
      (reserveBytes_some_iff base capacity used bytes (by omega) reservation).1 success
    subst reservation
    exact ⟨valid.1, valid.2.1, valid.2.2.1, checks.2.2.2.2⟩

theorem reserveBytes_interval (base capacity used bytes : Nat)
    (valid : Valid base capacity used) (positive : 0 < bytes)
    (reservation : Reservation)
    (success : reserveBytes base capacity used bytes = some reservation) :
    reservation.pointer = base + used ∧ reservation.used = used + bytes ∧
      used < reservation.used ∧ reservation.used ≤ capacity ∧
      0 < reservation.pointer ∧ reservation.pointer + bytes ≤ base + capacity := by
  obtain ⟨checks, same⟩ :=
    (reserveBytes_some_iff base capacity used bytes positive reservation).1 success
  subst reservation
  rcases valid with ⟨basePositive, capacityBound, addressBound, cursorBound⟩
  rcases checks with ⟨sizeBound, pointerBound, usedBound, endBound, fits⟩
  refine ⟨rfl, rfl, ?_, fits, ?_, ?_⟩
  · change used < used + bytes
    omega
  · change 0 < base + used
    omega
  · change base + used + bytes ≤ base + capacity
    omega

end SszNative.Arena
