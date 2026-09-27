import SszX86.NatAddCore
import SszX86.DelimitedReservation

namespace SszX86.NatAdd.Reservation.Large
open SszX86.NatAdd
open SszX86.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def flagged (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with status := flags}

def addressed (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r10 := UInt64.ofBitVec address
      r12 := UInt64.ofBitVec used
      r13 := UInt64.ofBitVec (used + address)}
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
      rbx := UInt64.ofBitVec ((s.regs.r13.toBitVec + 7#64) &&& ~~~7#64)
      r15 := UInt64.ofBitVec (paddingWord s.regs.r13.toBitVec + s.regs.r12.toBitVec)}
    status := flags}

theorem address_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address used : BitVec 64)
    (hb : Mem.loadInt s.dmem s.regs.r9.toBitVec 8 = some (address.toNat : Int))
    (hu : Mem.loadInt s.dmem (s.regs.r9.toBitVec + 16#64) 8 = some (used.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (addressed s address used flags,
        if used.toNat + address.toNat < 2^64 then base + 477 else base + 766)) :
    Eventually (step e) P (s, base + 458) := by
  have target := hc.targets ("natAdd_u766", 766) (by decide)
  natadd_step 119 using hc
  natadd_load hb
  natadd_step 120 using hc
  natadd_load hu
  natadd_step 121 using hc
  natadd_step 122 using hc
  natadd_step 123 using hc
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
      (flagged s flags, if s.regs.r13.toBitVec.toNat + 7 < 2^64
        then base + 487 else base + 766)) :
    Eventually (step e) P (s, base + 477) := by
  have target := hc.targets ("natAdd_u766", 766) (by decide)
  natadd_step 124 using hc
  natadd_step 125 using hc
  by_cases h : s.regs.r13.toNat + 7 < 2^64
  · have hn : ¬ (18446744073709551608 ≤ s.regs.r13.toNat ∧
        s.regs.r13.toBitVec ≠ 18446744073709551608#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r13.toNat = 18446744073709551608
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r13.toNat + 7 < 2^64 then base + 487 else base + 766) at hp
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : 18446744073709551608 ≤ s.regs.r13.toNat ∧
        s.regs.r13.toBitVec ≠ 18446744073709551608#64 := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.r13.toNat = 18446744073709551608 at he'
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r13.toNat + 7 < 2^64 then base + 487 else base + 766) at hp
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

/-- LEA+AND round the absolute address, SUB obtains the padding, and ADD/JB
checks the aligned cursor. AND's undefined AF is cut before SUB overwrites it. -/
theorem alignment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (alignedState s flags,
        if (paddingWord s.regs.r13.toBitVec).toNat + s.regs.r12.toBitVec.toNat < 2^64
        then base + 510 else base + 766)) :
    Eventually (step e) P (s, base + 487) := by
  have target := hc.targets ("natAdd_u766", 766) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with
          rbx := UInt64.ofBitVec ((s.regs.r13.toBitVec + 7#64) &&& ~~~7#64)}
        status := flags}, base + 495) := by
    natadd_step 128 using hc
    natadd_step 129 using hc
    natadd_step 130 using hc
    natadd_step 131 using hc
    by_cases h : (paddingWord s.regs.r13.toBitVec).toNat + s.regs.r12.toNat < 2^64
    · have hn : ¬ Udivti3.radix ≤ s.regs.r12.toNat +
          (paddingWord s.regs.r13.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_left h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord, StatusFlags.from_result, hn, Effects.All,
        UInt64.add_comm] using hp _
    · have hn : Udivti3.radix ≤ s.regs.r12.toNat +
          (paddingWord s.regs.r13.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_right h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, UintCodec.Arena.paddingWord, StatusFlags.from_result, hn, target, Effects.All,
        UInt64.add_comm] using hp _
  natadd_step 126 using hc
  natadd_step 127 using hc
  constructor <;> simpa [BitVec.ofInt_add, BitVec.ofInt_toInt] using rest _

def ended (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r14 := UInt64.ofBitVec (s.regs.r14.toBitVec + s.regs.r15.toBitVec)}
    status := flags}

/-- Checked payload-end addition. -/
theorem end_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (ended s flags,
        if s.regs.r14.toBitVec.toNat + s.regs.r15.toBitVec.toNat < 2^64
        then base + 519 else base + 766)) :
    Eventually (step e) P (s, base + 510) := by
  have target := hc.targets ("natAdd_u766", 766) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  natadd_step 132 using hc
  natadd_step 133 using hc
  by_cases h : s.regs.r14.toNat + s.regs.r15.toNat < 2^64
  · have hn : ¬ Udivti3.radix ≤ s.regs.r15.toNat + s.regs.r14.toNat := by
      dsimp [Udivti3.radix]; omega
    rw [ite_eq_left h] at hp
    simpa [ended, StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using hp _
  · have hn : Udivti3.radix ≤ s.regs.r15.toNat + s.regs.r14.toNat := by
      dsimp [Udivti3.radix]; omega
    rw [ite_eq_right h] at hp
    simpa [ended, StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using hp _

/-- The capacity is loaded from the original arena object, not assumed to fit. -/
theorem capacity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (capacity : BitVec 64)
    (hl : Mem.loadInt s.dmem (s.regs.r9.toBitVec + 8#64) 8 = some (capacity.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r14.toBitVec.toNat ≤ capacity.toNat
        then base + 529 else base + 766)) :
    Eventually (step e) P (s, base + 519) := by
  have target := hc.targets ("natAdd_u766", 766) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  natadd_step 134 using hc
  natadd_load hl
  natadd_step 135 using hc
  by_cases h : s.regs.r14.toNat ≤ capacity.toNat
  · have hn : ¬ (capacity.toNat ≤ s.regs.r14.toNat ∧ s.regs.r14.toBitVec ≠ capacity) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r14.toNat = capacity.toNat
      omega
    rw [ite_eq_left h] at hp
    simpa [StatusFlags.from_result, hn, flagged, Effects.All] using hp _
  · have hn : capacity.toNat ≤ s.regs.r14.toNat ∧ s.regs.r14.toBitVec ≠ capacity := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.r14.toNat = capacity.toNat at he'
      omega
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

def committed (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r10 := UInt64.ofBitVec (s.regs.r10.toBitVec + s.regs.r15.toBitVec)}
    dmem := Mem.storeInt s.dmem (s.regs.r9.toBitVec + 16#64) 8 s.regs.r14.toBitVec.toInt
    status := flags}

/-- The large reservation writes only the exact cursor word. -/
theorem commit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.r9.toBitVec + 16#64) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (committed s flags, base + 536)) :
    Eventually (step e) P (s, base + 529) := by
  natadd_step 136 using hc
  natadd_step 137 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · exact hm
  simp only [Effects.All]
  simpa [committed, UInt64.add_comm] using hp _

end SszX86.NatAdd.Reservation.Large
