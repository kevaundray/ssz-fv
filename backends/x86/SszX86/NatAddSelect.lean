import SszX86.NatAddCore

namespace SszX86.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- OR followed by CMP2 tests both significant counts, without truncating them. -/
theorem or_small_iff (a b : BitVec 64) :
    (a ||| b).toNat < 2 ↔ a.toNat ≤ 1 ∧ b.toNat ≤ 1 := by
  constructor
  · intro small
    have divided : (a ||| b).toNat / 2 = 0 := by omega
    rw [BitVec.toNat_or, Nat.or_div_two, Nat.or_eq_zero_iff] at divided
    omega
  · rintro ⟨left, right⟩
    have bound := Nat.or_lt_two_pow (n := 1) (x := a.toNat) (y := b.toNat)
      (by omega) (by omega)
    simpa only [BitVec.toNat_or] using bound

def sizeState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rbx := UInt64.ofBitVec (s.regs.rax.toBitVec ||| s.regs.r11.toBitVec)}
    status := flags}

theorem size_select_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (sizeState s flags, if s.regs.rax.toNat ≤ 1 ∧ s.regs.r11.toNat ≤ 1
        then base + 209 else base + 397)) :
    Eventually (step e) P (s, base + 193) := by
  have target := hc.targets ("natAdd_u397", 397) (by decide)
  have guard := or_small_iff s.regs.rax.toBitVec s.regs.r11.toBitVec
  natadd_step 55 using hc
  natadd_step 56 using hc
  constructor <;> natadd_step 57 using hc
  all_goals natadd_step 58 using hc
  all_goals
    by_cases small : s.regs.rax.toNat ≤ 1 ∧ s.regs.r11.toNat ≤ 1
    · have bound : (s.regs.rax.toBitVec ||| s.regs.r11.toBitVec).toNat < 2 := guard.mpr small
      have noBranch : ¬ 2 ≤ s.regs.rax.toNat ||| s.regs.r11.toNat := by
        change ¬ 2 ≤ s.regs.rax.toBitVec.toNat ||| s.regs.r11.toBitVec.toNat
        rw [← BitVec.toNat_or]
        omega
      simpa [StatusFlags.from_result, noBranch, sizeState, small, Effects.All,
        BitVec.or_comm, UInt64.toBitVec_or] using next _
    · have bound : 2 ≤ s.regs.rax.toNat ||| s.regs.r11.toNat := by
        change 2 ≤ s.regs.rax.toBitVec.toNat ||| s.regs.r11.toBitVec.toNat
        rw [← BitVec.toNat_or]
        have notSmall : ¬ (s.regs.rax.toBitVec ||| s.regs.r11.toBitVec).toNat < 2 := by
          intro h
          exact small (guard.mp h)
        omega
      simpa [StatusFlags.from_result, bound, target, sizeState, small, Effects.All,
        BitVec.or_comm, UInt64.toBitVec_or] using next _

/-- A nonzero Small contributes significant length one. The zero case reaches
the compiler's specialized zero-left dispatch without inspecting any limb. -/
theorem small_left_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (zero : s.regs.rdx.toBitVec = 0#64 → ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rdx := 0}, status := flags}, base + 130))
    (nonzero : s.regs.rdx.toBitVec ≠ 0#64 → ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rax := 1}, status := flags}, base + 70)) :
    Eventually (step e) P (s, base + 60) := by
  have target := hc.targets ("natAdd_u128", 128) (by decide)
  natadd_step 20 using hc
  constructor <;> natadd_step 21 using hc
  all_goals
    by_cases hz : s.regs.rdx.toBitVec = 0#64
    · simp [StatusFlags.from_result, hz, target, Effects.All]
      natadd_step 39 using hc
      constructor <;> exact zero hz _
    · simp [StatusFlags.from_result, hz, Effects.All]
      natadd_step 22 using hc
      exact nonzero hz _

/-- Zero-left's right-pointer dispatch chooses direct Small publication or the
same full Large count scan, explicitly clearing the left count first. -/
theorem zero_left_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rcx.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 390))
    (large : s.regs.rcx.toBitVec ≠ 0#64 → ∀ flags,
      Eventually (step e) P ({s with regs := {s.regs with rax := 0}, status := flags}, base + 141)) :
    Eventually (step e) P (s, base + 130) := by
  have target := hc.targets ("natAdd_u390", 390) (by decide)
  natadd_step 40 using hc
  constructor <;> natadd_step 41 using hc
  all_goals
    by_cases hz : s.regs.rcx.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using small hz _
    · simp [StatusFlags.from_result, hz, Effects.All]
      natadd_step 42 using hc
      constructor <;> exact large hz _

end SszX86.NatAdd
