import SszX86.MeasureOwned
import SszX86.NatFromU128Core

namespace SszX86.Measure.ProgressiveReservation
open SszX86.Delimited


def flagged (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with status := flags}

def addressed (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r9 := UInt64.ofBitVec address
      rdi := UInt64.ofBitVec used
      r8 := UInt64.ofBitVec (used + address)}
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
      rsi := UInt64.ofBitVec (paddingWord s.regs.r8.toBitVec + s.regs.rdi.toBitVec)}
    status := flags}

theorem address_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address used : BitVec 64)
    (hb : Mem.loadInt s.dmem s.regs.rcx.toBitVec 8 = some (address.toNat : Int))
    (hu : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + 16#64) 8 = some (used.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (addressed s address used flags,
        if used.toNat + address.toNat < 2^64 then base + 1444 else base + 2963)) :
    Eventually (step e) P (s, base + 1425) := by
  have target := hc.targets ("measure_u2963", 2963) (by decide)
  measure_step 165 using hc
  natfrom_load hb
  measure_step 166 using hc
  natfrom_load hu
  measure_step 167 using hc
  measure_step 168 using hc
  measure_step 169 using hc
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
      (flagged s flags, if s.regs.r8.toBitVec.toNat + 7 < 2^64
        then base + 1454 else base + 2963)) :
    Eventually (step e) P (s, base + 1444) := by
  have target := hc.targets ("measure_u2963", 2963) (by decide)
  measure_step 170 using hc
  measure_step 171 using hc
  by_cases h : s.regs.r8.toNat + 7 < 2^64
  · have hn : ¬ (18446744073709551608 ≤ s.regs.r8.toNat ∧
        s.regs.r8.toBitVec ≠ 18446744073709551608#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r8.toNat = 18446744073709551608
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r8.toNat + 7 < 2^64 then base + 1454 else base + 2963) at hp
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : 18446744073709551608 ≤ s.regs.r8.toNat ∧
        s.regs.r8.toBitVec ≠ 18446744073709551608#64 := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.r8.toNat = 18446744073709551608 at he'
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r8.toNat + 7 < 2^64 then base + 1454 else base + 2963) at hp
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

/-- LEA+AND round the absolute address, SUB obtains the padding, and ADD/JB
checks the aligned cursor. AND's undefined AF is cut before SUB overwrites it. -/
theorem alignment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (alignedState s flags,
        if (paddingWord s.regs.r8.toBitVec).toNat + s.regs.rdi.toBitVec.toNat < 2^64
        then base + 1474 else base + 2963)) :
    Eventually (step e) P (s, base + 1454) := by
  have target := hc.targets ("measure_u2963", 2963) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with
          rsi := UInt64.ofBitVec ((s.regs.r8.toBitVec + 7#64) &&& ~~~7#64)}
        status := flags}, base + 1462) := by
    measure_step 174 using hc
    measure_step 175 using hc
    measure_step 176 using hc
    by_cases h : (paddingWord s.regs.r8.toBitVec).toNat + s.regs.rdi.toNat < 2^64
    · have hn : ¬ Udivti3.radix ≤ s.regs.rdi.toNat +
          (paddingWord s.regs.r8.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_left h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord, StatusFlags.from_result, hn, Effects.All,
        UInt64.add_comm] using hp _
    · have hn : Udivti3.radix ≤ s.regs.rdi.toNat +
          (paddingWord s.regs.r8.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_right h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord, StatusFlags.from_result, hn, target, Effects.All,
        UInt64.add_comm] using hp _
  measure_step 172 using hc
  measure_step 173 using hc
  constructor <;> simpa [BitVec.ofInt_add, BitVec.ofInt_toInt] using rest _

/-- CMP -17 / JA implements the positive sixteen-byte end guard exactly. -/
theorem end_guard_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rsi.toBitVec.toNat + 16 < 2^64
        then base + 1484 else base + 2963)) :
    Eventually (step e) P (s, base + 1474) := by
  have target := hc.targets ("measure_u2963", 2963) (by decide)
  measure_step 177 using hc
  measure_step 178 using hc
  by_cases h : s.regs.rsi.toNat + 16 < 2^64
  · have hn : ¬ (18446744073709551599 ≤ s.regs.rsi.toNat ∧
        s.regs.rsi.toBitVec ≠ 18446744073709551599#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.rsi.toNat = 18446744073709551599
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rsi.toNat + 16 < 2^64 then base + 1484 else base + 2963) at hp
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : 18446744073709551599 ≤ s.regs.rsi.toNat ∧
        s.regs.rsi.toBitVec ≠ 18446744073709551599#64 := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.rsi.toNat = 18446744073709551599 at he'
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rsi.toNat + 16 < 2^64 then base + 1484 else base + 2963) at hp
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

def ended (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rdi := UInt64.ofBitVec (s.regs.rsi.toBitVec + 16)}}

theorem end_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step e) P (ended s, base + 1488)) :
    Eventually (step e) P (s, base + 1484) := by
  measure_step 179 using hc
  simpa [ended, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_comm] using hp

/-- The capacity is loaded from the original arena object, not assumed to fit. -/
theorem capacity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (capacity : BitVec 64)
    (hl : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + 8#64) 8 = some (capacity.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rdi.toBitVec.toNat ≤ capacity.toNat
        then base + 1498 else base + 2963)) :
    Eventually (step e) P (s, base + 1488) := by
  have target := hc.targets ("measure_u2963", 2963) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  measure_step 180 using hc
  natfrom_load hl
  measure_step 181 using hc
  by_cases h : s.regs.rdi.toNat ≤ capacity.toNat
  · have hn : ¬ (capacity.toNat ≤ s.regs.rdi.toNat ∧ s.regs.rdi.toBitVec ≠ capacity) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.rdi.toNat = capacity.toNat
      omega
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : capacity.toNat ≤ s.regs.rdi.toNat ∧ s.regs.rdi.toBitVec ≠ capacity := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.rdi.toNat = capacity.toNat at he'
      omega
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

end SszX86.Measure.ProgressiveReservation
