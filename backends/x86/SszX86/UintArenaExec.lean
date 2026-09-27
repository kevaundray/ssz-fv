import SszX86.UintWidth
import SszX86.Udivti3Math
import SszArena

namespace SszX86.UintCodec.Arena
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Only flags are forgotten at a CPS cut. Every cut quantifies all flags. -/
def flagged (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with status := flags}

def prepared (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (8#64 + (s.regs.r10.toBitVec >>> 3) * 8#64)
      r10 := UInt64.ofBitVec (s.regs.r10.toBitVec >>> 3)}
    status := flags}

def addressed (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r9 := UInt64.ofBitVec address
      r8 := UInt64.ofBitVec used
      r11 := UInt64.ofBitVec (used + address)}
    status := flags}

def paddingWord (address : BitVec 64) : BitVec 64 :=
  ((address + 7#64) &&& ~~~7#64) - address

private theorem padding_raw (v : UInt64) :
    (paddingWord v.toBitVec).toNat =
      (18446744073709551616 - v.toNat +
        ((v.toNat + 7) % 18446744073709551616 &&& 18446744073709551608)) %
          18446744073709551616 := by
  simp [paddingWord]

def alignedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rcx := UInt64.ofBitVec (paddingWord s.regs.r11.toBitVec + s.regs.r8.toBitVec)}
    status := flags}

def ended (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (s.regs.rax.toBitVec + s.regs.rcx.toBitVec)}
    status := flags}

/-- The only data-memory write in the entire prefix is the cursor commit. -/
def committed (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsi := s.regs.r14
      r8 := UInt64.ofBitVec (s.regs.r10.toBitVec + 1#64)
      r9 := UInt64.ofBitVec (s.regs.r9.toBitVec + s.regs.rcx.toBitVec)
      r11 := 0
      rbx := s.regs.rbp
      r14 := 0}
    status := flags
    dmem := Mem.storeInt s.dmem (s.regs.rbx.toBitVec + 16#64) 8 s.regs.rax.toBitVec.toInt}

private theorem shift_cast (v : UInt64) :
    BitVec.ofInt 64 ((v.toNat : Int) >>> 3) = v.toBitVec >>> 3 := by
  change BitVec.ofNat 64 (v.toBitVec >>> 3).toNat = _
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem sign_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rax.toNat < 2^63 then base + 5526 else base + 2918)) :
    Eventually (step e) P (s, base + 2908) := by
  have target := hc.targets ("u2918", 2918) (by decide)
  uint_width_step 83 using hc
  constructor <;> uint_width_step 84 using hc
  all_goals
    by_cases h : s.regs.rax.toNat < 2^63
    · have hn : ¬ 2^63 ≤ s.regs.rax.toNat := by omega
      rw [ite_eq_left h] at hp
      simp [StatusFlags.from_result, BitVec.msb_eq_decide, hn, Effects.All]
      uint_width_step 85 using hc
      simpa [flagged] using hp _
    · have hn : 2^63 ≤ s.regs.rax.toNat := by omega
      rw [ite_eq_right h] at hp
      simpa [StatusFlags.from_result, BitVec.msb_eq_decide, hn, target,
        flagged, Effects.All] using hp _

/-- SHR 3, scaled LEA, TEST, JL, and the real long jump. Each undefined-flag
site is cut before proceeding, so the suffix is never expanded exponentially. -/
theorem preparation_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (prepared s flags, if (8#64 + (s.regs.r10.toBitVec >>> 3) * 8#64).toNat < 2^63
        then base + 5526 else base + 2918)) :
    Eventually (step e) P (s, base + 2896) := by
  have tested (flags : StatusFlags) : Eventually (step e) P (prepared s flags, base + 2908) := by
    apply sign_cps e base hc
    intro flags'
    simpa only [flagged, prepared, UInt64.toNat_ofBitVec] using hp flags'
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with r10 := UInt64.ofBitVec (s.regs.r10.toBitVec >>> 3)}
        status := flags}, base + 2900) := by
    uint_width_step 82 using hc
    simpa [prepared, BitVec.ofInt_add, BitVec.ofInt_mul, shift_cast,
      BitVec.add_comm, UInt64.add_comm] using tested flags
  uint_width_step 81 using hc
  simp (config := {instances := true})
    [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp, BitVec.take, Effects.All]
  repeat' apply And.intro
  all_goals exact rest _

/-- The first checked addition, before any mutation or alignment. -/
theorem address_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address used : BitVec 64)
    (hb : Mem.loadInt s.dmem s.regs.rbx.toBitVec 8 = some (address.toNat : Int))
    (hu : Mem.loadInt s.dmem (s.regs.rbx.toBitVec + 16#64) 8 = some (used.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (addressed s address used flags,
        if used.toNat + address.toNat < 2^64 then base + 5545 else base + 2918)) :
    Eventually (step e) P (s, base + 5526) := by
  have target := hc.targets ("u2918", 2918) (by decide)
  uint_width_step 164 using hc
  uint_width_load hb
  uint_width_step 165 using hc
  uint_width_load hu
  uint_width_step 166 using hc
  uint_width_step 167 using hc
  uint_width_step 168 using hc
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
        then base + 5555 else base + 2918)) :
    Eventually (step e) P (s, base + 5545) := by
  have target := hc.targets ("u2918", 2918) (by decide)
  uint_width_step 169 using hc
  uint_width_step 170 using hc
  by_cases h : s.regs.r11.toNat + 7 < 2^64
  · have hn : ¬ (18446744073709551608 ≤ s.regs.r11.toNat ∧
        s.regs.r11.toBitVec ≠ 18446744073709551608#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r11.toNat = 18446744073709551608
      omega
    change ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r11.toNat + 7 < 2^64 then base + 5555 else base + 2918) at hp
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
      (flagged s flags, if s.regs.r11.toNat + 7 < 2^64 then base + 5555 else base + 2918) at hp
    rw [ite_eq_right h] at hp
    simpa [StatusFlags.from_result, hn, target, flagged, Effects.All] using hp _

/-- LEA+AND round the absolute address, SUB obtains the padding, and ADD/JB
checks the aligned cursor. AND's undefined AF is cut before SUB overwrites it. -/
theorem alignment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (alignedState s flags,
        if (paddingWord s.regs.r11.toBitVec).toNat + s.regs.r8.toBitVec.toNat < 2^64
        then base + 5575 else base + 2918)) :
    Eventually (step e) P (s, base + 5555) := by
  have target := hc.targets ("u2918", 2918) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with
          rcx := UInt64.ofBitVec ((s.regs.r11.toBitVec + 7#64) &&& ~~~7#64)}
        status := flags}, base + 5563) := by
    uint_width_step 173 using hc
    uint_width_step 174 using hc
    uint_width_step 175 using hc
    by_cases h : (paddingWord s.regs.r11.toBitVec).toNat + s.regs.r8.toNat < 2^64
    · have hn : ¬ Udivti3.radix ≤ s.regs.r8.toNat +
          (paddingWord s.regs.r11.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_left h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, StatusFlags.from_result, hn, Effects.All,
        UInt64.add_comm] using hp _
    · have hn : Udivti3.radix ≤ s.regs.r8.toNat +
          (paddingWord s.regs.r11.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_right h] at hp
      rw [padding_raw] at hn
      simpa [alignedState, paddingWord, StatusFlags.from_result, hn, target, Effects.All,
        UInt64.add_comm] using hp _
  uint_width_step 171 using hc
  uint_width_step 172 using hc
  constructor <;> simpa [BitVec.ofInt_add, BitVec.ofInt_toInt] using rest _

/-- Checked payload-end addition. -/
theorem end_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (ended s flags,
        if s.regs.rax.toBitVec.toNat + s.regs.rcx.toBitVec.toNat < 2^64
        then base + 5584 else base + 2918)) :
    Eventually (step e) P (s, base + 5575) := by
  have target := hc.targets ("u2918", 2918) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  uint_width_step 176 using hc
  uint_width_step 177 using hc
  by_cases h : s.regs.rax.toNat + s.regs.rcx.toNat < 2^64
  · have hn : ¬ Udivti3.radix ≤ s.regs.rcx.toNat + s.regs.rax.toNat := by
      dsimp [Udivti3.radix]; omega
    rw [ite_eq_left h] at hp
    simpa [ended, StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using hp _
  · have hn : Udivti3.radix ≤ s.regs.rcx.toNat + s.regs.rax.toNat := by
      dsimp [Udivti3.radix]; omega
    rw [ite_eq_right h] at hp
    simpa [ended, StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using hp _

/-- The capacity is loaded from the original arena object, not assumed to fit. -/
theorem capacity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (capacity : BitVec 64)
    (hl : Mem.loadInt s.dmem (s.regs.rbx.toBitVec + 8#64) 8 = some (capacity.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rax.toBitVec.toNat ≤ capacity.toNat
        then base + 5594 else base + 2918)) :
    Eventually (step e) P (s, base + 5584) := by
  have target := hc.targets ("u2918", 2918) (by decide)
  simp only [UInt64.toNat_toBitVec] at hp
  uint_width_step 178 using hc
  uint_width_load hl
  uint_width_step 179 using hc
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

/-- Commit exactly the used slot, establish the packing registers, and execute
the linked jump to 5647. Neither payload nor output nor stack is written. -/
theorem commit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rbx.toBitVec + 16#64) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (committed s flags, base + 5647)) :
    Eventually (step e) P (s, base + 5594) := by
  obtain ⟨old, hl⟩ := hm
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with
          rsi := s.regs.r14
          r8 := UInt64.ofBitVec (s.regs.r10.toBitVec + 1#64)
          r9 := UInt64.ofBitVec (s.regs.r9.toBitVec + s.regs.rcx.toBitVec)
          r11 := 0}
        status := flags
        dmem := Mem.storeInt s.dmem (s.regs.rbx.toBitVec + 16#64) 8 s.regs.rax.toBitVec.toInt},
        base + 5611) := by
    uint_width_step 185 using hc
    uint_width_step 186 using hc
    constructor <;> uint_width_step 187 using hc
    all_goals simpa [committed] using hp _
  uint_width_step 180 using hc
  uint_width_step 181 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  uint_width_step 182 using hc
  simp (config := {instances := true})
    [BitVec.ofInt_add, BitVec.ofInt_toInt, MachineData.store,
     Width.bytes, Width.bits, hl, Effects.All]
  uint_width_step 183 using hc
  uint_width_step 184 using hc
  constructor <;> simpa [BitVec.ofInt_add, BitVec.ofInt_toInt, UInt64.add_comm] using rest _

end SszX86.UintCodec.Arena
