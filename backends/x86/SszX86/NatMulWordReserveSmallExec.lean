import SszX86.NatMulWordCore
import SszX86.DelimitedReservation

namespace SszX86.NatMulWord.SmallReservation
open SszX86.NatMulWord
open SszX86.Delimited


def flagged (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with status := flags}

def addressed (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rcx := UInt64.ofBitVec address
      r9 := UInt64.ofBitVec used
      r10 := UInt64.ofBitVec (used + address)}
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
      rsi := UInt64.ofBitVec (paddingWord s.regs.r10.toBitVec + s.regs.r9.toBitVec)}
    status := flags}

theorem address_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address used : BitVec 64)
    (hb : Mem.loadInt s.dmem s.regs.r8.toBitVec 8 = some (address.toNat : Int))
    (hu : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16#64) 8 = some (used.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (addressed s address used flags,
        if used.toNat + address.toNat < 2^64 then base + 542 else base + 617)) :
    Eventually (step e) P (s, base + 527) := by
  have target := hc.targets ("natMulWord_u617", 617) (by decide)
  natmulword_step 4:12 using hc
  natmulword_load hb
  natmulword_step 4:13 using hc
  natmulword_load hu
  natmulword_step 4:14 using hc
  natmulword_step 4:15 using hc
  natmulword_step 4:16 using hc
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
      (flagged s flags, if s.regs.r10.toBitVec.toNat + 7 < 2^64
        then base + 548 else base + 617)) :
    Eventually (step e) P (s, base + 542) := by
  have target := hc.targets ("natMulWord_u617", 617) (by decide)
  natmulword_step 4:17 using hc
  natmulword_step 4:18 using hc
  by_cases h : s.regs.r10.toNat + 7 < 2^64
  · have hn : ¬ (18446744073709551608 ≤ s.regs.r10.toNat ∧
        s.regs.r10.toBitVec ≠ 18446744073709551608#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r10.toNat = 18446744073709551608
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r10.toNat + 7 < 2^64 then base + 548 else base + 617) at hp
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : 18446744073709551608 ≤ s.regs.r10.toNat ∧
        s.regs.r10.toBitVec ≠ 18446744073709551608#64 := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.r10.toNat = 18446744073709551608 at he'
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r10.toNat + 7 < 2^64 then base + 548 else base + 617) at hp
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

/-- LEA+AND round the absolute address, SUB obtains the padding, and ADD/JB
checks the aligned cursor. AND's undefined AF is cut before SUB overwrites it. -/
theorem alignment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (alignedState s flags,
        if (paddingWord s.regs.r10.toBitVec).toNat + s.regs.r9.toBitVec.toNat < 2^64
        then base + 564 else base + 617)) :
    Eventually (step e) P (s, base + 548) := by
  have target := hc.targets ("natMulWord_u617", 617) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with
          rsi := UInt64.ofBitVec ((s.regs.r10.toBitVec + 7#64) &&& ~~~7#64)}
        status := flags}, base + 556) := by
    natmulword_step 4:21 using hc
    natmulword_step 4:22 using hc
    natmulword_step 4:23 using hc
    by_cases h : (paddingWord s.regs.r10.toBitVec).toNat + s.regs.r9.toNat < 2^64
    · have hn : ¬ Udivti3.radix ≤ s.regs.r9.toNat +
          (paddingWord s.regs.r10.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_left h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord, StatusFlags.from_result, hn, Effects.All,
        UInt64.add_comm] using hp _
    · have hn : Udivti3.radix ≤ s.regs.r9.toNat +
          (paddingWord s.regs.r10.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_right h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord, StatusFlags.from_result, hn, target, Effects.All,
        UInt64.add_comm] using hp _
  natmulword_step 4:19 using hc
  natmulword_step 4:20 using hc
  constructor <;> simpa [BitVec.ofInt_add, BitVec.ofInt_toInt] using rest _

/-- CMP -17 / JA implements the positive sixteen-byte end guard exactly. -/
theorem end_guard_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rsi.toBitVec.toNat + 16 < 2^64
        then base + 570 else base + 617)) :
    Eventually (step e) P (s, base + 564) := by
  have target := hc.targets ("natMulWord_u617", 617) (by decide)
  natmulword_step 4:24 using hc
  natmulword_step 4:25 using hc
  by_cases h : s.regs.rsi.toNat + 16 < 2^64
  · have hn : ¬ (18446744073709551599 ≤ s.regs.rsi.toNat ∧
        s.regs.rsi.toBitVec ≠ 18446744073709551599#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.rsi.toNat = 18446744073709551599
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rsi.toNat + 16 < 2^64 then base + 570 else base + 617) at hp
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
      (flagged s flags, if s.regs.rsi.toNat + 16 < 2^64 then base + 570 else base + 617) at hp
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

def ended (s : MachineData) : MachineData :=
  {s with regs := {s.regs with r9 := UInt64.ofBitVec (s.regs.rsi.toBitVec + 16)}}

theorem end_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step e) P (ended s, base + 574)) :
    Eventually (step e) P (s, base + 570) := by
  natmulword_step 4:26 using hc
  simpa [ended, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_comm] using hp

/-- The capacity is loaded from the original arena object, not assumed to fit. -/
theorem capacity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (capacity : BitVec 64)
    (hl : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 8#64) 8 = some (capacity.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r9.toBitVec.toNat ≤ capacity.toNat
        then base + 580 else base + 617)) :
    Eventually (step e) P (s, base + 574) := by
  have target := hc.targets ("natMulWord_u617", 617) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  natmulword_step 4:27 using hc
  natmulword_load hl
  natmulword_step 4:28 using hc
  by_cases h : s.regs.r9.toNat ≤ capacity.toNat
  · have hn : ¬ (capacity.toNat ≤ s.regs.r9.toNat ∧ s.regs.r9.toBitVec ≠ capacity) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r9.toNat = capacity.toNat
      omega
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : capacity.toNat ≤ s.regs.r9.toNat ∧ s.regs.r9.toBitVec ≠ capacity := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.r9.toNat = capacity.toNat at he'
      omega
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

end SszX86.NatMulWord.SmallReservation
