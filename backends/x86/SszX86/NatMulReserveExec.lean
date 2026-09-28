import SszX86.NatMulCore
import SszX86.DelimitedReservation

namespace SszX86.NatMul.Reservation
open SszX86.Delimited

set_option maxHeartbeats 16000000

def flagged (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with status := flags}

def addressed (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r15 := UInt64.ofBitVec address
      r11 := UInt64.ofBitVec used
      rbx := UInt64.ofBitVec (used + address)}
    status := flags}

abbrev paddingWord := UintCodec.Arena.paddingWord

private theorem padding_raw (v : UInt64) :
    (paddingWord v.toBitVec).toNat =
      (18446744073709551616 - v.toNat +
        ((v.toNat + 7) % 18446744073709551616 &&& 18446744073709551608)) %
          18446744073709551616 := by
  simp [paddingWord, UintCodec.Arena.paddingWord]

def alignedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r8 := UInt64.ofBitVec (paddingWord s.regs.rbx.toBitVec + s.regs.r11.toBitVec)}
    status := flags}

theorem address_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address used : BitVec 64)
    (hb : Mem.loadInt s.dmem s.regs.r9.toBitVec 8 = some (address.toNat : Int))
    (hu : Mem.loadInt s.dmem (s.regs.r9.toBitVec + 16#64) 8 = some (used.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (addressed s address used flags,
        if used.toNat + address.toNat < 2^64 then base + 408 else base + 318)) :
    Eventually (step e) P (s, base + 393) := by
  have target := hc.targets ("natMul_u318", 318) (by decide)
  natmul_step 3 row 15 using hc
  natmul_load hb
  natmul_step 3 row 16 using hc
  natmul_load hu
  natmul_step 3 row 17 using hc
  natmul_step 3 row 18 using hc
  natmul_step 3 row 19 using hc
  by_cases h : used.toNat + address.toNat < 2^64
  · have hn : ¬ Udivti3.radix ≤ address.toNat + used.toNat := by dsimp [Udivti3.radix]; omega
    rw [ite_eq_left h] at hp
    simpa [addressed, StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using hp _
  · have hn : Udivti3.radix ≤ address.toNat + used.toNat := by dsimp [Udivti3.radix]; omega
    rw [ite_eq_right h] at hp
    simpa [addressed, StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using hp _

/-- CMP -8 / JA is precisely the checked address+7 guard, including equality. -/
theorem rounding_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rbx.toBitVec.toNat + 7 < 2^64
        then base + 414 else base + 318)) :
    Eventually (step e) P (s, base + 408) := by
  have target := hc.targets ("natMul_u318", 318) (by decide)
  natmul_step 3 row 20 using hc
  natmul_step 3 row 21 using hc
  by_cases h : s.regs.rbx.toNat + 7 < 2^64
  · have hn : ¬ (18446744073709551608 ≤ s.regs.rbx.toNat ∧
        s.regs.rbx.toBitVec ≠ 18446744073709551608#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.rbx.toNat = 18446744073709551608
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rbx.toNat + 7 < 2^64 then base + 414 else base + 318) at hp
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : 18446744073709551608 ≤ s.regs.rbx.toNat ∧
        s.regs.rbx.toBitVec ≠ 18446744073709551608#64 := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.rbx.toNat = 18446744073709551608 at he'
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rbx.toNat + 7 < 2^64 then base + 414 else base + 318) at hp
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

/-- Absolute-address alignment followed by checked cursor padding. -/
theorem alignment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (alignedState s flags,
        if (paddingWord s.regs.rbx.toBitVec).toNat + s.regs.r11.toNat < 2^64
        then base + 430 else base + 318)) :
    Eventually (step e) P (s, base + 414) := by
  have target := hc.targets ("natMul_u318", 318) (by decide)
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with
          r8 := UInt64.ofBitVec ((s.regs.rbx.toBitVec + 7#64) &&& ~~~7#64)}
        status := flags}, base + 422) := by
    natmul_step 3 row 24 using hc
    natmul_step 3 row 25 using hc
    natmul_step 3 row 26 using hc
    by_cases h : (paddingWord s.regs.rbx.toBitVec).toNat + s.regs.r11.toNat < 2^64
    · have hn : ¬ Udivti3.radix ≤ s.regs.r11.toNat +
          (paddingWord s.regs.rbx.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_left h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord,
        StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using hp _
    · have hn : Udivti3.radix ≤ s.regs.r11.toNat +
          (paddingWord s.regs.rbx.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_right h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord,
        StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using hp _
  natmul_step 3 row 22 using hc
  natmul_step 3 row 23 using hc
  constructor <;> simpa [BitVec.ofInt_add, BitVec.ofInt_toInt] using rest _

def ended (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r11 := UInt64.ofBitVec (s.regs.r8.toBitVec + s.regs.rdx.toBitVec)}
    status := flags}

/-- Checked payload-end addition. -/
theorem end_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (ended s flags,
        if s.regs.r8.toBitVec.toNat + s.regs.rdx.toBitVec.toNat < 2^64
        then base + 438 else base + 318)) :
    Eventually (step e) P (s, base + 430) := by
  have target := hc.targets ("natMul_u318", 318) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  natmul_step 3 row 27 using hc
  natmul_step 3 row 28 using hc
  natmul_step 3 row 29 using hc
  by_cases h : s.regs.r8.toNat + s.regs.rdx.toNat < 2^64
  · have hn : ¬ Udivti3.radix ≤ s.regs.rdx.toNat + s.regs.r8.toNat := by
      dsimp [Udivti3.radix]; omega
    rw [ite_eq_left h] at hp
    simpa [ended, StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using hp _
  · have hn : Udivti3.radix ≤ s.regs.rdx.toNat + s.regs.r8.toNat := by
      dsimp [Udivti3.radix]; omega
    rw [ite_eq_right h] at hp
    simpa [ended, StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using hp _

/-- The capacity is loaded from the original arena object, not assumed to fit. -/
theorem capacity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (capacity : BitVec 64)
    (hl : Mem.loadInt s.dmem (s.regs.r9.toBitVec + 8#64) 8 = some (capacity.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r11.toBitVec.toNat ≤ capacity.toNat
        then base + 444 else base + 318)) :
    Eventually (step e) P (s, base + 438) := by
  have target := hc.targets ("natMul_u318", 318) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  natmul_step 3 row 30 using hc
  natmul_load hl
  natmul_step 3 row 31 using hc
  by_cases h : s.regs.r11.toNat ≤ capacity.toNat
  · have hn : ¬ (capacity.toNat ≤ s.regs.r11.toNat ∧ s.regs.r11.toBitVec ≠ capacity) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r11.toNat = capacity.toNat
      omega
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : capacity.toNat ≤ s.regs.r11.toNat ∧ s.regs.r11.toBitVec ≠ capacity := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.r11.toNat = capacity.toNat at he'
      omega
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

end SszX86.NatMul.Reservation
