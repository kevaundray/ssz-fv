import SszArm.BitVectorContract

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

/-- Every small writable interval lies inside one permitted large interval. -/
def Covers (large small : List Span) : Prop :=
  ∀ span ∈ small, ∃ outer ∈ large, outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2

theorem Covers.refl (writes : List Span) : Covers writes writes := by
  intro span member
  exact ⟨span, member, Nat.le_refl _, Nat.le_refl _⟩

theorem Covers.trans {first second third : List Span}
    (left : Covers first second) (right : Covers second third) : Covers first third := by
  intro span member
  obtain ⟨middle, middleMember, middleLow, middleHigh⟩ := right span member
  obtain ⟨outer, outerMember, outerLow, outerHigh⟩ := left middle middleMember
  exact ⟨outer, outerMember, by omega, by omega⟩

theorem Covers.protected {large small : List Span} (cover : Covers large small)
    {address bytes : Nat} (owned : Protected large address bytes) :
    Protected small address bytes := by
  rcases owned with empty | separate
  · exact Or.inl empty
  · right
    intro span member
    obtain ⟨outer, outerMember, low, high⟩ := cover span member
    have disjoint := separate outer outerMember
    omega

theorem Covers.frame {large small : List Span} (cover : Covers large small)
    {s t : ArmState} (frame : MemoryFrame small s t) : MemoryFrame large s t := by
  intro address outside
  apply frame address
  intro span member
  obtain ⟨outer, outerMember, low, high⟩ := cover span member
  have disjoint := outside outer outerMember
  omega

theorem Covers.operand {large small : List Span} (cover : Covers large small)
    (operand : SszNative.NatOperand) (owned : NatDivision.OperandOwned large operand) :
    NatDivision.OperandOwned small operand := by
  cases operand with
  | small word => trivial
  | large pointer words => exact cover.protected owned

theorem local_covered (s : ArmState) (result : SszNative.BitVector.Outcome) :
    Covers (writesFor s result) (localWrites s) := by
  intro span member
  exact ⟨span, by simp only [writesFor, List.mem_append]; exact Or.inl (Or.inl member),
    Nat.le_refl _, Nat.le_refl _⟩

theorem allocated_covered (s : ArmState) (result : SszNative.BitVector.Outcome) :
    Covers (writesFor s result) result.writes := by
  intro span member
  exact ⟨span, by simp only [writesFor, List.mem_append]; exact Or.inr member,
    Nat.le_refl _, Nat.le_refl _⟩

/-- The first reservation remains present after every subsequent branch. -/
theorem divided_eq (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (arena : SszNative.Delimited.ArenaState) :
    (SszNative.BitVector.run length data arena).divided =
      SszNative.NatDivision.run length 8 arena.base arena.capacity arena.used := by
  cases divided : (SszNative.NatDivision.run length 8 arena.base arena.capacity arena.used).result with
  | error reason => simp only [SszNative.BitVector.run, divided]
  | ok pair =>
    rcases pair with ⟨quotient, remainder⟩
    by_cases zero : remainder = 0
    · simp only [SszNative.BitVector.run, divided, zero, ↓reduceIte]
    · cases rounded : (SszNative.NatAdd.run quotient (.small 1) arena.base arena.capacity
        (SszNative.NatDivision.run length 8 arena.base arena.capacity arena.used).used).result <;>
        simp only [SszNative.BitVector.run, divided, zero, ↓reduceIte, rounded]

theorem divided_write (s : ArmState) (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (reservation : SszNative.Arena.Reservation)
    (allocated : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).allocation = some reservation) :
    (reservation.pointer, 8 * (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).written.length) ∈ (outcome s length data).writes := by
  apply List.mem_append_left
  simp only [outcome, SszNative.BitVector.Outcome.writes, divided_eq,
    SszNative.BitVector.allocationWrites, allocated, List.mem_singleton]

theorem cursor_covered (s : ArmState) (result : SszNative.BitVector.Outcome)
    (allocated : result.writes ≠ []) :
    Covers (writesFor s result) [((r (.GPR 19#5) s).toNat + 16, 8)] := by
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  refine ⟨((r (.GPR 19#5) s).toNat + 16, 8), ?_, Nat.le_refl _, Nat.le_refl _⟩
  simp [writesFor, allocated]

/-- Recover original readonly bytes and representations from the checked byte
frame, rather than requiring preservation as a separate execution assumption. -/
theorem post_of_frame (s t : ArmState) (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (owned : Owned s length data) (returned : Returned s t)
    (result : SszNative.BitVector.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
      (r (.GPR 2#5) s).toNat data (outcome s length data).result)
    (written : (outcome s length data).writtenAt (widthLoad t))
    (cursor : (read_mem_bytes 8 (r (.GPR 19#5) s + 16#64) t).toNat =
      (outcome s length data).used)
    (arenaBase : read_mem_bytes 8 (r (.GPR 19#5) s) t =
      read_mem_bytes 8 (r (.GPR 19#5) s) s)
    (arenaCapacity : read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) t =
      read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) s)
    (frame : MemoryFrame (writesFor s (outcome s length data)) s t) :
    Post s t length data := by
  refine ⟨returned, result, written, cursor, arenaBase, arenaCapacity, frame,
    NatDivision.operand_preserved frame length owned.descriptor.2.2 owned.operandOwned,
    ?_, ?_, ?_⟩
  · intro index within
    have bound := owned.inputBound
    rw [frame.load _ 1 (by omega) (owned.inputOwned.subspan index 1 (by omega))]
    exact owned.input index within
  · intro address low high
    exact frame.protected_byte owned.inputOwned address low high
  · intro address low high
    exact frame.protected_byte owned.descriptorOwned address low high

end SszArm.BitVector
