import SszX86.NatAddReserveLargeExec

namespace SszX86.NatAdd.Reservation.Large
open SszX86.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def maxState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax :=
      if s.regs.rax.toNat < s.regs.r11.toNat then s.regs.r11 else s.regs.rax}
    status := flags}

/-- The actual unsigned CMOVA selects the maximum before checked count+1. -/
theorem max_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (maxState s flags, if max s.regs.rax.toNat s.regs.r11.toNat = 2^64 - 1
        then base + 1399 else base + 414)) :
    Eventually (step e) P (s, base + 397) := by
  have target := hc.targets ("natAdd_u1399", 1399) (by decide)
  natadd_step 106 using hc
  natadd_step 107 using hc
  by_cases h : s.regs.rax.toNat < s.regs.r11.toNat
  · have cmp : s.regs.rax.toNat ≤ s.regs.r11.toNat ∧
        s.regs.r11.toBitVec ≠ s.regs.rax.toBitVec := by
      refine ⟨by omega, ?_⟩
      intro he
      have := congrArg BitVec.toNat he
      simp only [UInt64.toNat_toBitVec] at this
      omega
    simp [StatusFlags.from_result, cmp]
    natadd_step 108 using hc
    natadd_step 109 using hc
    have mx : max s.regs.rax.toNat s.regs.r11.toNat = s.regs.r11.toNat := by omega
    have eq : s.regs.r11.toBitVec = 18446744073709551615#64 ↔
        s.regs.r11.toNat = 2^64 - 1 := by
      rw [← BitVec.toNat_inj]
      rfl
    simp only [maxState, h, ite_true, mx] at hp
    by_cases ov : s.regs.r11.toNat = 18446744073709551615 <;>
      simpa [StatusFlags.from_result, eq, ov, target, Effects.All] using hp _
  · have cmp : ¬ (s.regs.rax.toNat ≤ s.regs.r11.toNat ∧
        s.regs.r11.toBitVec ≠ s.regs.rax.toBitVec) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r11.toNat = s.regs.rax.toNat
      omega
    simp [StatusFlags.from_result, cmp]
    natadd_step 108 using hc
    natadd_step 109 using hc
    have mx : max s.regs.rax.toNat s.regs.r11.toNat = s.regs.rax.toNat := by omega
    have eq : s.regs.rax.toBitVec = 18446744073709551615#64 ↔
        s.regs.rax.toNat = 2^64 - 1 := by
      rw [← BitVec.toNat_inj]
      rfl
    simp only [maxState, h, ite_false, mx] at hp
    by_cases ov : s.regs.rax.toNat = 18446744073709551615 <;>
      simpa [StatusFlags.from_result, eq, ov, target, Effects.All] using hp _

def lengthState (s : MachineData) (scratch10 scratchBX : UInt64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r11 := 2305843009213693950
      r10 := scratch10
      rbx := scratchBX
      r14 := UInt64.ofBitVec (s.regs.rax.toBitVec * 8#64 + 8#64)}
    status := flags}

private theorem length_iff (n : UInt64) :
    (n.toNat ≤ 2305843009213693950 ∧
      (n.toBitVec * 8#64 + 8#64).toNat < 2^63) ↔
      8 * (n.toNat + 1) < 2^63 := by
  have hn := n.toBitVec.isLt
  have wordNat : (n.toBitVec * 8#64 + 8#64).toNat =
      (8 * (n.toNat + 1)) % 2^64 := by
    simp [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod, Nat.mul_mod,
      Nat.mul_add, Nat.mul_comm]
  rw [wordNat]
  constructor
  · rintro ⟨bound, sign⟩
    have noOverflow : 8 * (n.toNat + 1) < 2^64 := by omega
    rwa [Nat.mod_eq_of_lt noOverflow] at sign
  · intro bound
    exact ⟨by omega, by rw [Nat.mod_eq_of_lt (by omega)]; exact bound⟩

/-- Scaled LEA and ADD form the byte count. SETA checks multiplication overflow;
TEST/SETL checks isize, and OR combines them without any signed capacity bound. -/
theorem length_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ scratch10 scratchBX flags, Eventually (step e) P
      (lengthState s scratch10 scratchBX flags,
        if 8 * (s.regs.rax.toNat + 1) < 2^63 then base + 458 else base + 766)) :
    Eventually (step e) P (s, base + 414) := by
  have target := hc.targets ("natAdd_u766", 766) (by decide)
  have eq : s.regs.rax.toBitVec = 2305843009213693950#64 ↔
      s.regs.rax.toNat = 2305843009213693950 := by
    rw [← BitVec.toNat_inj]
    rfl
  have mulCond :
      (!decide (s.regs.rax.toNat < 2305843009213693950) &&
        !decide (s.regs.rax.toBitVec = 2305843009213693950#64)) =
      decide (¬ s.regs.rax.toNat ≤ 2305843009213693950) := by
    apply Bool.eq_iff_iff.mpr
    simp [eq] <;> omega
  have byteNat : (s.regs.rax.toBitVec * 8#64 + 8#64).toNat =
      (8 + s.regs.rax.toNat * 8) % 18446744073709551616 := by
    simp [Nat.add_comm]
  simp only [← length_iff, byteNat] at hp
  natadd_step 110 using hc
  natadd_step 111 using hc
  natadd_step 112 using hc
  natadd_step 113 using hc
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natadd_step 114 using hc
  natadd_step 115 using hc
  constructor <;> natadd_step 116 using hc
  all_goals
    natadd_step 117 using hc
    constructor <;> natadd_step 118 using hc
  all_goals
    by_cases hm : s.regs.rax.toNat ≤ 2305843009213693950 <;>
      by_cases hs : (8 + s.regs.rax.toNat * 8) % 18446744073709551616 < 9223372036854775808
    all_goals
      have sign : (9223372036854775808 ≤
          (8 + s.regs.rax.toNat * 8) % 18446744073709551616) ↔
          ¬ (8 + s.regs.rax.toNat * 8) % 18446744073709551616 < 9223372036854775808 := by omega
      simpa [lengthState, StatusFlags.from_result, BitVec.msb_eq_decide,
        mulCond, sign, hm, hs, target, Effects.All, BitVec.replaceLow, BitVec.drop,
        BitVec.take, NatCompare.byte_append, NatCompare.byte_extract,
        UInt64.add_comm] using hp _ _ _

end SszX86.NatAdd.Reservation.Large
