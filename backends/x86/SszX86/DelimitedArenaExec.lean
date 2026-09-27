import SszX86.DelimitedCore

namespace SszX86.Delimited.Reservation
open SszX86.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def flagged (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with status := flags}

def addressed (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec address
      r10 := UInt64.ofBitVec used
      r11 := UInt64.ofBitVec (used + address)}
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
      r9 := UInt64.ofBitVec (paddingWord s.regs.r11.toBitVec + s.regs.r10.toBitVec)}
    status := flags}

theorem address_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address used : BitVec 64)
    (hb : Mem.loadInt s.dmem s.regs.r8.toBitVec 8 = some (address.toNat : Int))
    (hu : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16#64) 8 = some (used.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (addressed s address used flags,
        if used.toNat + address.toNat < 2^64 then base + 288 else base + 736)) :
    Eventually (step e) P (s, base + 269) := by
  have target := hc.targets ("delimited_u736", 736) (by decide)
  delimited_step 62 using hc
  delimited_load hb
  delimited_step 63 using hc
  delimited_load hu
  delimited_step 64 using hc
  delimited_step 65 using hc
  delimited_step 66 using hc
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
      (flagged s flags, if s.regs.r11.toBitVec.toNat + 7 < 2^64
        then base + 298 else base + 736)) :
    Eventually (step e) P (s, base + 288) := by
  have target := hc.targets ("delimited_u736", 736) (by decide)
  delimited_step 67 using hc
  delimited_step 68 using hc
  by_cases h : s.regs.r11.toNat + 7 < 2^64
  · have hn : ¬ (18446744073709551608 ≤ s.regs.r11.toNat ∧
        s.regs.r11.toBitVec ≠ 18446744073709551608#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r11.toNat = 18446744073709551608
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r11.toNat + 7 < 2^64 then base + 298 else base + 736) at hp
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : 18446744073709551608 ≤ s.regs.r11.toNat ∧
        s.regs.r11.toBitVec ≠ 18446744073709551608#64 := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.r11.toNat = 18446744073709551608 at he'
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r11.toNat + 7 < 2^64 then base + 298 else base + 736) at hp
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

/-- LEA+AND round the absolute address, SUB obtains the padding, and ADD/JB
checks the aligned cursor. AND's undefined AF is cut before SUB overwrites it. -/
theorem alignment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (alignedState s flags,
        if (paddingWord s.regs.r11.toBitVec).toNat + s.regs.r10.toBitVec.toNat < 2^64
        then base + 318 else base + 736)) :
    Eventually (step e) P (s, base + 298) := by
  have target := hc.targets ("delimited_u736", 736) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with
          r9 := UInt64.ofBitVec ((s.regs.r11.toBitVec + 7#64) &&& ~~~7#64)}
        status := flags}, base + 306) := by
    delimited_step 71 using hc
    delimited_step 72 using hc
    delimited_step 73 using hc
    by_cases h : (paddingWord s.regs.r11.toBitVec).toNat + s.regs.r10.toNat < 2^64
    · have hn : ¬ Udivti3.radix ≤ s.regs.r10.toNat +
          (paddingWord s.regs.r11.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_left h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord, StatusFlags.from_result, hn, Effects.All,
        UInt64.add_comm] using hp _
    · have hn : Udivti3.radix ≤ s.regs.r10.toNat +
          (paddingWord s.regs.r11.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_right h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord, StatusFlags.from_result, hn, target, Effects.All,
        UInt64.add_comm] using hp _
  delimited_step 69 using hc
  delimited_step 70 using hc
  constructor <;> simpa [BitVec.ofInt_add, BitVec.ofInt_toInt] using rest _

/-- CMP -17 / JA implements the positive sixteen-byte end guard exactly. -/
theorem end_guard_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r9.toBitVec.toNat + 16 < 2^64
        then base + 328 else base + 736)) :
    Eventually (step e) P (s, base + 318) := by
  have target := hc.targets ("delimited_u736", 736) (by decide)
  delimited_step 74 using hc
  delimited_step 75 using hc
  by_cases h : s.regs.r9.toNat + 16 < 2^64
  · have hn : ¬ (18446744073709551599 ≤ s.regs.r9.toNat ∧
        s.regs.r9.toBitVec ≠ 18446744073709551599#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r9.toNat = 18446744073709551599
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r9.toNat + 16 < 2^64 then base + 328 else base + 736) at hp
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : 18446744073709551599 ≤ s.regs.r9.toNat ∧
        s.regs.r9.toBitVec ≠ 18446744073709551599#64 := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.r9.toNat = 18446744073709551599 at he'
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r9.toNat + 16 < 2^64 then base + 328 else base + 736) at hp
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

def ended (s : MachineData) : MachineData :=
  {s with regs := {s.regs with r10 := UInt64.ofBitVec (s.regs.r9.toBitVec + 16)}}

theorem end_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step e) P (ended s, base + 332)) :
    Eventually (step e) P (s, base + 328) := by
  delimited_step 76 using hc
  simpa [ended, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_comm] using hp

/-- The capacity is loaded from the original arena object, not assumed to fit. -/
theorem capacity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (capacity : BitVec 64)
    (hl : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 8#64) 8 = some (capacity.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r10.toBitVec.toNat ≤ capacity.toNat
        then base + 342 else base + 736)) :
    Eventually (step e) P (s, base + 332) := by
  have target := hc.targets ("delimited_u736", 736) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  delimited_step 77 using hc
  delimited_load hl
  delimited_step 78 using hc
  by_cases h : s.regs.r10.toNat ≤ capacity.toNat
  · have hn : ¬ (capacity.toNat ≤ s.regs.r10.toNat ∧ s.regs.r10.toBitVec ≠ capacity) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r10.toNat = capacity.toNat
      omega
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : capacity.toNat ≤ s.regs.r10.toNat ∧ s.regs.r10.toBitVec ≠ capacity := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.r10.toNat = capacity.toNat at he'
      omega
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

end SszX86.Delimited.Reservation
