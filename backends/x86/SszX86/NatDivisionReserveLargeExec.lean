import SszX86.NatDivisionCore
import SszX86.DelimitedReservation

namespace SszX86.NatDivision.Reservation.Large
open SszX86.NatDivision
open SszX86.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def flagged (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with status := flags}

def addressed (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r14 := UInt64.ofBitVec address
      r11 := UInt64.ofBitVec used
      r15 := UInt64.ofBitVec (used + address)}
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
      r9 := UInt64.ofBitVec ((s.regs.r15.toBitVec + 7#64) &&& ~~~7#64)
      rdi := UInt64.ofBitVec (paddingWord s.regs.r15.toBitVec + s.regs.r11.toBitVec)}
    status := flags}

theorem address_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address used : BitVec 64)
    (hb : Mem.loadInt s.dmem s.regs.r12.toBitVec 8 = some (address.toNat : Int))
    (hu : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16#64) 8 = some (used.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (addressed s address used flags,
        if used.toNat + address.toNat < 2^64 then base + 569 else base + 205)) :
    Eventually (step e) P (s, base + 548) := by
  have target := hc.targets ("natDivision_u205", 205) (by decide)
  natdiv_step 143 using hc
  natdiv_load hb
  natdiv_step 144 using hc
  natdiv_load hu
  natdiv_step 145 using hc
  natdiv_step 146 using hc
  natdiv_step 147 using hc
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
      (flagged s flags, if s.regs.r15.toBitVec.toNat + 7 < 2^64
        then base + 579 else base + 205)) :
    Eventually (step e) P (s, base + 569) := by
  have target := hc.targets ("natDivision_u205", 205) (by decide)
  natdiv_step 148 using hc
  natdiv_step 149 using hc
  by_cases h : s.regs.r15.toNat + 7 < 2^64
  · have hn : ¬ (18446744073709551608 ≤ s.regs.r15.toNat ∧
        s.regs.r15.toBitVec ≠ 18446744073709551608#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r15.toNat = 18446744073709551608
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r15.toNat + 7 < 2^64 then base + 579 else base + 205) at hp
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : 18446744073709551608 ≤ s.regs.r15.toNat ∧
        s.regs.r15.toBitVec ≠ 18446744073709551608#64 := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.r15.toNat = 18446744073709551608 at he'
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r15.toNat + 7 < 2^64 then base + 579 else base + 205) at hp
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

/-- LEA+AND round the absolute address, SUB obtains the padding, and ADD/JB
checks the aligned cursor. AND's undefined AF is cut before SUB overwrites it. -/
theorem alignment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (alignedState s flags,
        if (paddingWord s.regs.r15.toBitVec).toNat + s.regs.r11.toBitVec.toNat < 2^64
        then base + 602 else base + 205)) :
    Eventually (step e) P (s, base + 579) := by
  have target := hc.targets ("natDivision_u205", 205) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with
          r9 := UInt64.ofBitVec ((s.regs.r15.toBitVec + 7#64) &&& ~~~7#64)}
        status := flags}, base + 587) := by
    natdiv_step 152 using hc
    natdiv_step 153 using hc
    natdiv_step 154 using hc
    natdiv_step 155 using hc
    by_cases h : (paddingWord s.regs.r15.toBitVec).toNat + s.regs.r11.toNat < 2^64
    · have hn : ¬ Udivti3.radix ≤ s.regs.r11.toNat +
          (paddingWord s.regs.r15.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_left h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord, StatusFlags.from_result, hn, Effects.All,
        UInt64.add_comm] using hp _
    · have hn : Udivti3.radix ≤ s.regs.r11.toNat +
          (paddingWord s.regs.r15.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_right h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord, StatusFlags.from_result, hn, target, Effects.All,
        UInt64.add_comm] using hp _
  natdiv_step 150 using hc
  natdiv_step 151 using hc
  constructor <;> simpa [BitVec.ofInt_add, BitVec.ofInt_toInt] using rest _

def ended (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r10 := UInt64.ofBitVec (s.regs.r10.toBitVec + s.regs.rdi.toBitVec)}
    status := flags}

/-- Checked payload-end addition. -/
theorem end_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (ended s flags,
        if s.regs.r10.toBitVec.toNat + s.regs.rdi.toBitVec.toNat < 2^64
        then base + 611 else base + 205)) :
    Eventually (step e) P (s, base + 602) := by
  have target := hc.targets ("natDivision_u205", 205) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  natdiv_step 156 using hc
  natdiv_step 157 using hc
  by_cases h : s.regs.r10.toNat + s.regs.rdi.toNat < 2^64
  · have hn : ¬ Udivti3.radix ≤ s.regs.rdi.toNat + s.regs.r10.toNat := by
      dsimp [Udivti3.radix]; omega
    rw [ite_eq_left h] at hp
    simpa [ended, StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using hp _
  · have hn : Udivti3.radix ≤ s.regs.rdi.toNat + s.regs.r10.toNat := by
      dsimp [Udivti3.radix]; omega
    rw [ite_eq_right h] at hp
    simpa [ended, StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using hp _

/-- The capacity is loaded from the original arena object, not assumed to fit. -/
theorem capacity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (capacity : BitVec 64)
    (hl : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 8#64) 8 = some (capacity.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r10.toBitVec.toNat ≤ capacity.toNat
        then base + 622 else base + 205)) :
    Eventually (step e) P (s, base + 611) := by
  have target := hc.targets ("natDivision_u205", 205) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  natdiv_step 158 using hc
  natdiv_load hl
  natdiv_step 159 using hc
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

def committed (s : MachineData) : MachineData :=
  {s with
    dmem := Mem.storeInt s.dmem (s.regs.r12.toBitVec + 16#64) 8
      s.regs.r10.toBitVec.toInt}

/-- Only the used cursor is written; copying starts at the following INC. -/
theorem commit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16#64) 8 = some old)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (committed s, base + 627)) :
    Eventually (step e) P (s, base + 622) := by
  natdiv_step 160 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · exact hm
  simp only [Effects.All]
  simpa [committed] using hp

end SszX86.NatDivision.Reservation.Large
