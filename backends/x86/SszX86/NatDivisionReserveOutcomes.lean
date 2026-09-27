import SszX86.NatDivisionReserveMemory

namespace SszX86.NatDivision.Reservation

private theorem small_exits_ne (base : Int64) : base + 379 ≠ base + 358 := by
  intro equal
  have difference := congrArg (fun pc : Int64 => pc - base) equal
  simp only [Int64.add_comm base 379, Int64.add_comm base 358,
    Int64.add_sub_cancel] at difference
  exact (show (379 : Int64) ≠ 358 by decide) difference

private theorem large_exits_ne (base : Int64) : base + 205 ≠ base + 627 := by
  intro equal
  have difference := congrArg (fun pc : Int64 => pc - base) equal
  simp only [Int64.add_comm base 205, Int64.add_comm base 627,
    Int64.add_sub_cancel] at difference
  exact (show (205 : Int64) ≠ 627 by decide) difference

/-- Every all-effects endpoint reports failure iff the source reserve fails,
and succeeds iff the source reserve returns an allocation. -/
theorem Small.outcomes (s : MachineData) (base : Int64)
    (address capacity used : BitVec 64) (st : MachineState)
    (post : Small.Post s base address capacity used st) :
    (st.2 = base + 379 ↔ SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = none) ∧
    (st.2 = base + 358 ↔ ∃ allocation,
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some allocation) := by
  rcases post.2 with ⟨failed, pc, _⟩ | ⟨allocation, reserved, pc, _⟩
  · constructor
    · exact ⟨fun _ => failed, fun _ => pc⟩
    · constructor
      · intro other
        exact False.elim (small_exits_ne base (pc.symm.trans other))
      · rintro ⟨allocation, reserved⟩
        rw [failed] at reserved
        contradiction
  · constructor
    · constructor
      · intro other
        exact False.elim (small_exits_ne base (other.symm.trans pc))
      · intro failed
        rw [reserved] at failed
        contradiction
    · exact ⟨fun _ => ⟨allocation, reserved⟩, fun _ => pc⟩

/-- Complete resource adequacy for the real large-count reservation, with no
signed restriction on capacity and no existential choice of undefined flags. -/
theorem Large.outcomes (s : MachineData) (base : Int64)
    (address capacity used : BitVec 64) (st : MachineState)
    (post : Large.Post s base address capacity used st) :
    (st.2 = base + 205 ↔ SszNative.Arena.reserve address.toNat capacity.toNat used.toNat s.regs.rax.toNat = none) ∧
    (st.2 = base + 627 ↔ ∃ allocation,
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat s.regs.rax.toNat = some allocation) := by
  rcases post.2 with ⟨failed, pc, _⟩ | ⟨allocation, reserved, pc, _⟩
  · constructor
    · exact ⟨fun _ => failed, fun _ => pc⟩
    · constructor
      · intro other
        exact False.elim (large_exits_ne base (pc.symm.trans other))
      · rintro ⟨allocation, reserved⟩
        rw [failed] at reserved
        contradiction
  · constructor
    · constructor
      · intro other
        exact False.elim (large_exits_ne base (other.symm.trans pc))
      · intro failed
        rw [reserved] at failed
        contradiction
    · exact ⟨fun _ => ⟨allocation, reserved⟩, fun _ => pc⟩

end SszX86.NatDivision.Reservation
