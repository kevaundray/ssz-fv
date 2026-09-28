import SszX86.NatMulReserveArena

namespace SszX86.NatMul.Reservation
open SszNative

def total (s : MachineData) : Nat := s.regs.r12.toNat + s.regs.r13.toNat

def allocatedState (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  reservedState (countState s s.status) address used flags

def Failed (s : MachineData) (base : Int64) (address capacity used : BitVec 64)
    (t : MachineState) : Prop :=
  Frame s t.1 ∧ t.1.dmem = s.dmem ∧
  ((¬ total s < 2^64 ∧ t.2 = base + 746) ∨
    (total s < 2^64 ∧ Arena.reserve address.toNat capacity.toNat used.toNat (total s) = none ∧
      t.2 = base + 318))

def CheckedPost (s : MachineData) (base : Int64) (address capacity used : BitVec 64)
    (t : MachineState) : Prop :=
  Failed s base address capacity used t ∨
  (total s < 2^64 ∧ ∃ r,
    Arena.reserve address.toNat capacity.toNat used.toNat (total s) = some r ∧
    t.2 = base + 444 ∧ ∃ flags, t.1 = allocatedState s address used flags)

private theorem frame_count (s : MachineData) (flags : StatusFlags) : Frame s (countState s flags) := by
  refine ⟨rfl, ?_⟩
  intro reg h1 h2 h3 h4 h5 h6
  cases reg <;> simp_all [countState, Reg64s.get64]

theorem Frame.trans {s t u : MachineData} (first : Frame s t) (second : Frame t u) : Frame s u := by
  refine ⟨second.1.trans first.1, ?_⟩
  intro reg h1 h2 h3 h4 h5 h6
  exact (second.2 reg h1 h2 h3 h4 h5 h6).trans (first.2 reg h1 h2 h3 h4 h5 h6)

theorem counted_nat (s : MachineData) (flags : StatusFlags) (bound : total s < 2^64) :
    (countState s flags).regs.r14.toNat = total s := by
  have sum : s.regs.r13.toNat + s.regs.r12.toNat < 2^64 := by unfold total at bound; omega
  simpa [countState, total, Nat.add_comm] using
    UintCodec.Arena.add_nat s.regs.r13.toBitVec s.regs.r12.toBitVec sum

/-- All count and resource failure alternatives are retained. In particular this
is not a successful-allocation precondition disguised as a continuation. -/
theorem checked_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address capacity used : BitVec 64)
    (header : Header s address capacity used) (positive : 0 < total s) :
    Eventually (step e) (CheckedPost s base address capacity used) (s, base + 275) := by
  apply count_cps e base hc
  intro f0
  change Eventually (step e) _
    (countState s f0, if total s < 2^64 then base + 287 else base + 746)
  by_cases bound : total s < 2^64
  · rw [ite_eq_left bound]
    have natural := counted_nat s f0 bound
    have run := guards_runs e base hc (countState s f0) address capacity used
      ⟨header.address_load, header.capacity_load, header.used_load⟩ (by rw [natural]; exact positive)
    apply eventually_weaken (step e) _ _ _ _ run
    intro t post
    rcases post.2 with failure | ⟨r, reserved, pc, flags, state⟩
    · exact Or.inl ⟨(frame_count s f0).trans post.1, failure.2.2,
        Or.inr ⟨bound, by simpa only [natural] using failure.1, failure.2.1⟩⟩
    · refine Or.inr ⟨bound, r, by simpa only [natural] using reserved, pc, flags, ?_⟩
      simpa only [allocatedState, reservedState, countState] using state
  · rw [ite_eq_right bound]
    exact Eventually.done _ (Or.inl ⟨frame_count s f0, rfl, Or.inl ⟨bound, rfl⟩⟩)

/-- Failure dispatch agrees with the checked significant-count model. -/
theorem failed_model (s : MachineData) (base : Int64) (address capacity used : BitVec 64)
    (left right : NatOperand) (lc : s.regs.r12.toNat = left.wordCount)
    (rc : s.regs.r13.toNat = right.wordCount)
    (hl : 1 < left.wordCount) (hr : 1 < right.wordCount)
    (t : MachineState) (failed : Failed s base address capacity used t) :
    SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.unchanged used.toNat (.error .scratchExhausted) := by
  have counts : total s = left.wordCount + right.wordCount := by simp [total, lc, rc]
  rw [SszNative.NatMul.run_large left right _ _ _ hl hr]
  rcases failed.2.2 with ⟨overflow, _⟩ | ⟨bound, none, _⟩
  · simp only [counts] at overflow
    rw [ite_eq_right overflow]
  · simp only [counts] at bound none
    rw [ite_eq_left bound, none]

/-- The same successful reservation, including its full untrimmed limb count,
is the checked model's allocation. -/
theorem reserved_model (s : MachineData) (address capacity used : BitVec 64)
    (left right : NatOperand) (lc : s.regs.r12.toNat = left.wordCount)
    (rc : s.regs.r13.toNat = right.wordCount)
    (hl : 1 < left.wordCount) (hr : 1 < right.wordCount)
    (bound : total s < 2^64) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat (total s) = some r) :
    SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatMul.writtenWords left right) := by
  have counts : total s = left.wordCount + right.wordCount := by simp [total, lc, rc]
  simp only [counts] at bound reserved
  rw [SszNative.NatMul.run_large left right _ _ _ hl hr, ite_eq_left bound, reserved]

end SszX86.NatMul.Reservation
