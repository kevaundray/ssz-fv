import SszX86.CodecMeasureFixedArithmeticResources

namespace SszX86.CodecMeasureFixed
open SszNative

/-- A checked complete written buffer lies above the old cursor and below the
committed cursor. The one-past-end arena bound excludes machine-address wrap. -/
theorem arithmetic_written_geometry {α : Type} (call : NatArithmetic.Outcome α)
    (base capacity used : Nat) (reservation : Arena.Reservation)
    (arenaBound : base + capacity ≤ 2 ^ 64)
    (checks : Arena.Checks base capacity used call.written.length)
    (pointer : reservation.pointer = base + Arena.start base used)
    (cursor : call.used = Arena.finish base used call.written.length)
    (a : BitVec 64)
    (span : Emit.InSpan a (BitVec.ofNat 64 reservation.pointer) (8 * call.written.length)) :
    base + used ≤ a.toNat ∧ a.toNat < base + call.used ∧ call.used ≤ capacity := by
  obtain ⟨i, index, address⟩ := span
  have startBound := Arena.used_le_start base used
  have capacityBound := checks.2.2.2.2.2
  have endEq : base + call.used = reservation.pointer + 8 * call.written.length := by
    rw [cursor, pointer, Arena.finish]
    omega
  have noWrap : reservation.pointer + i < 2 ^ 64 := by
    rw [← cursor] at capacityBound
    omega
  have observed : a.toNat = reservation.pointer + i := by
    rw [address, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt noWrap]
  rw [observed]
  rw [← cursor] at capacityBound
  exact ⟨by omega, by omega, capacityBound⟩

theorem add_writes_geometry (left right : NatOperand) (base capacity used : Nat)
    (arenaBound : base + capacity ≤ 2 ^ 64) (a : BitVec 64)
    (writes : ArithmeticWrites (SszNative.NatAdd.run left right base capacity used) a) :
    base + used ≤ a.toNat ∧
      a.toNat < base + (SszNative.NatAdd.run left right base capacity used).used ∧
      (SszNative.NatAdd.run left right base capacity used).used ≤ capacity := by
  obtain ⟨reservation, allocated, span⟩ := writes
  obtain ⟨checks, pointer, cursor, count⟩ :=
    SszNative.NatAdd.allocation_geometry left right base capacity used reservation allocated
  exact arithmetic_written_geometry _ base capacity used reservation arenaBound checks pointer cursor a span

theorem mul_writes_geometry (left right : NatOperand) (base capacity used : Nat)
    (arenaBound : base + capacity ≤ 2 ^ 64) (a : BitVec 64)
    (writes : ArithmeticWrites (SszNative.NatMul.run left right base capacity used) a) :
    base + used ≤ a.toNat ∧
      a.toNat < base + (SszNative.NatMul.run left right base capacity used).used ∧
      (SszNative.NatMul.run left right base capacity used).used ≤ capacity := by
  obtain ⟨reservation, allocated, span⟩ := writes
  obtain ⟨checks, pointer, cursor⟩ :=
    SszNative.NatMul.allocation_geometry left right base capacity used reservation allocated
  exact arithmetic_written_geometry _ base capacity used reservation arenaBound checks pointer cursor a span

theorem divide8_writes_geometry (operand : NatOperand) (base capacity used : Nat)
    (arenaBound : base + capacity ≤ 2 ^ 64) (a : BitVec 64)
    (writes : ArithmeticWrites (SszNative.NatDivision.run operand 8 base capacity used) a) :
    base + used ≤ a.toNat ∧
      a.toNat < base + (SszNative.NatDivision.run operand 8 base capacity used).used ∧
      (SszNative.NatDivision.run operand 8 base capacity used).used ≤ capacity := by
  obtain ⟨reservation, allocated, span⟩ := writes
  obtain ⟨usedEq, lengthEq, checks, pointer, cursor, result⟩ :=
    SszNative.NatDivision.allocation_resources operand 8 base capacity used reservation allocated
  apply arithmetic_written_geometry _ base capacity used reservation arenaBound _ pointer _ a span
  · simpa only [lengthEq] using checks
  · simpa only [lengthEq, usedEq] using cursor

/-- Pure addition cursor bounds also cover all nonallocating errors and borrowed
zero-input branches, without importing provider ownership. -/
theorem add_cursor_bounds (left right : NatOperand) (base capacity used : Nat)
    (bound : used ≤ capacity) :
    used ≤ (SszNative.NatAdd.run left right base capacity used).used ∧
      (SszNative.NatAdd.run left right base capacity used).used ≤ capacity := by
  cases allocation : (SszNative.NatAdd.run left right base capacity used).allocation with
  | none =>
    rw [(SszNative.NatAdd.no_allocation_resources left right base capacity used allocation).1]
    exact ⟨Nat.le_refl _, bound⟩
  | some reservation =>
    obtain ⟨checks, pointer, cursor, count⟩ :=
      SszNative.NatAdd.allocation_geometry left right base capacity used reservation allocation
    rw [cursor]
    have lower := Arena.used_le_start base used
    exact ⟨by unfold Arena.finish; omega, checks.2.2.2.2.2⟩

theorem divide8_cursor_bounds (operand : NatOperand) (base capacity used : Nat)
    (bound : used ≤ capacity) :
    used ≤ (SszNative.NatDivision.run operand 8 base capacity used).used ∧
      (SszNative.NatDivision.run operand 8 base capacity used).used ≤ capacity := by
  cases allocation : (SszNative.NatDivision.run operand 8 base capacity used).allocation with
  | none =>
    rw [(SszNative.NatDivision.no_allocation_resources operand 8 base capacity used allocation).1]
    exact ⟨Nat.le_refl _, bound⟩
  | some reservation =>
    obtain ⟨usedEq, lengthEq, checks, pointer, cursor, result⟩ :=
      SszNative.NatDivision.allocation_resources operand 8 base capacity used reservation allocation
    rw [usedEq, cursor]
    have lower := Arena.used_le_start base used
    exact ⟨by unfold Arena.finish; omega, checks.2.2.2.2.2⟩

end SszX86.CodecMeasureFixed
