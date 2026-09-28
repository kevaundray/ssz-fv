import SszX86.NatMulWordCore
import SszX86.DelimitedReservation

namespace SszX86.NatMulWord.LargeReservation
open SszX86.NatMulWord
open SszX86.Delimited


def flagged (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with status := flags}

def addressed (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r14 := UInt64.ofBitVec address
      rdx := UInt64.ofBitVec used
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
      rbp := UInt64.ofBitVec ((s.regs.r10.toBitVec + 7#64) &&& ~~~7#64)
      r13 := UInt64.ofBitVec (paddingWord s.regs.r10.toBitVec + s.regs.rdx.toBitVec)}
    status := flags}

theorem address_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address used : BitVec 64)
    (hb : Mem.loadInt s.dmem s.regs.r8.toBitVec 8 = some (address.toNat : Int))
    (hu : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16#64) 8 = some (used.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (addressed s address used flags,
        if used.toNat + address.toNat < 2^64 then base + 258 else base + 617)) :
    Eventually (step e) P (s, base + 239) := by
  have target := hc.targets ("natMulWord_u617", 617) (by decide)
  natmulword_step 1:29 using hc
  natmulword_load hb
  natmulword_step 1:30 using hc
  natmulword_load hu
  natmulword_step 1:31 using hc
  natmulword_step 2:0 using hc
  natmulword_step 2:1 using hc
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
        then base + 268 else base + 617)) :
    Eventually (step e) P (s, base + 258) := by
  have target := hc.targets ("natMulWord_u617", 617) (by decide)
  natmulword_step 2:2 using hc
  natmulword_step 2:3 using hc
  by_cases h : s.regs.r10.toNat + 7 < 2^64
  · have hn : ¬ (18446744073709551608 ≤ s.regs.r10.toNat ∧
        s.regs.r10.toBitVec ≠ 18446744073709551608#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r10.toNat = 18446744073709551608
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r10.toNat + 7 < 2^64 then base + 268 else base + 617) at hp
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
      (flagged s flags, if s.regs.r10.toNat + 7 < 2^64 then base + 268 else base + 617) at hp
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

/-- LEA+AND round the absolute address, SUB obtains the padding, and ADD/JB
checks the aligned cursor. AND's undefined AF is cut before SUB overwrites it. -/
theorem alignment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (alignedState s flags,
        if (paddingWord s.regs.r10.toBitVec).toNat + s.regs.rdx.toBitVec.toNat < 2^64
        then base + 291 else base + 617)) :
    Eventually (step e) P (s, base + 268) := by
  have target := hc.targets ("natMulWord_u617", 617) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with
          rbp := UInt64.ofBitVec ((s.regs.r10.toBitVec + 7#64) &&& ~~~7#64)}
        status := flags}, base + 276) := by
    natmulword_step 2:6 using hc
    natmulword_step 2:7 using hc
    natmulword_step 2:8 using hc
    natmulword_step 2:9 using hc
    by_cases h : (paddingWord s.regs.r10.toBitVec).toNat + s.regs.rdx.toNat < 2^64
    · have hn : ¬ Udivti3.radix ≤ s.regs.rdx.toNat +
          (paddingWord s.regs.r10.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_left h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord, StatusFlags.from_result, hn, Effects.All,
        UInt64.add_comm] using hp _
    · have hn : Udivti3.radix ≤ s.regs.rdx.toNat +
          (paddingWord s.regs.r10.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_right h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord, StatusFlags.from_result, hn, target, Effects.All,
        UInt64.add_comm] using hp _
  natmulword_step 2:4 using hc
  natmulword_step 2:5 using hc
  constructor <;> simpa [BitVec.ofInt_add, BitVec.ofInt_toInt] using rest _

def ended (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (s.regs.rax.toBitVec + s.regs.r13.toBitVec)}
    status := flags}

/-- Checked payload-end addition. -/
theorem end_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (ended s flags,
        if s.regs.rax.toBitVec.toNat + s.regs.r13.toBitVec.toNat < 2^64
        then base + 300 else base + 617)) :
    Eventually (step e) P (s, base + 291) := by
  have target := hc.targets ("natMulWord_u617", 617) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  natmulword_step 2:10 using hc
  natmulword_step 2:11 using hc
  by_cases h : s.regs.rax.toNat + s.regs.r13.toNat < 2^64
  · have hn : ¬ Udivti3.radix ≤ s.regs.r13.toNat + s.regs.rax.toNat := by
      dsimp [Udivti3.radix]; omega
    rw [ite_eq_left h] at hp
    simpa [ended, StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using hp _
  · have hn : Udivti3.radix ≤ s.regs.r13.toNat + s.regs.rax.toNat := by
      dsimp [Udivti3.radix]; omega
    rw [ite_eq_right h] at hp
    simpa [ended, StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using hp _

/-- The capacity is loaded from the original arena object, not assumed to fit. -/
theorem capacity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (capacity : BitVec 64)
    (hl : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 8#64) 8 = some (capacity.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rax.toBitVec.toNat ≤ capacity.toNat
        then base + 310 else base + 617)) :
    Eventually (step e) P (s, base + 300) := by
  have target := hc.targets ("natMulWord_u617", 617) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  natmulword_step 2:12 using hc
  natmulword_load hl
  natmulword_step 2:13 using hc
  by_cases h : s.regs.rax.toNat ≤ capacity.toNat
  · have hn : ¬ (capacity.toNat ≤ s.regs.rax.toNat ∧ s.regs.rax.toBitVec ≠ capacity) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.rax.toNat = capacity.toNat
      omega
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : capacity.toNat ≤ s.regs.rax.toNat ∧ s.regs.rax.toBitVec ≠ capacity := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.rax.toNat = capacity.toNat at he'
      omega
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

end SszX86.NatMulWord.LargeReservation
