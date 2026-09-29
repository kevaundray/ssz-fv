import SszX86.CodecMeasurePartsDecode
import SszX86.DelimitedReservation
import SszTypedArena

namespace SszX86.CodecMeasureParts
open UintCodec

abbrev paddingWord := UintCodec.Arena.paddingWord

def flagged (s : MachineData) (flags : StatusFlags) : MachineData := {s with status := flags}

def addressed (s : MachineData) (address used : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsi := UInt64.ofBitVec address
      rcx := UInt64.ofBitVec used
      rdx := UInt64.ofBitVec (used + address)}
    status := flags}

def aligned (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    r13 := UInt64.ofBitVec ((s.regs.rdx.toBitVec + 7) &&& ~~~7#64),
    rax := UInt64.ofBitVec (paddingWord s.regs.rdx.toBitVec + s.regs.rcx.toBitVec)}, status := flags}

def ended (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rcx := UInt64.ofBitVec (s.regs.rbx.toBitVec * 40 + s.regs.rax.toBitVec)}, status := flags}

structure Header (s : MachineData) (address capacity used : BitVec 64) : Prop where
  address_load : Mem.loadInt s.dmem s.regs.r14.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 8) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 16) 8 = some (used.toNat : Int)

/-- The first checked address addition executes before any Plan initialization. -/
theorem address_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (address used : BitVec 64)
    (hb : Mem.loadInt s.dmem s.regs.r14.toBitVec 8 = some (address.toNat : Int))
    (hu : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 16) 8 = some (used.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (addressed s address used flags,
        if used.toNat + address.toNat < 2 ^ 64 then base + 350 else base + 1021)) :
    Eventually (step e) P (s, base + 331) := by
  have target := code.targets ("codec_measure_parts_u1021", 1021) (by decide)
  codec_measure_parts_step 74 using code
  codec_measure_parts_load hb
  codec_measure_parts_step 75 using code
  codec_measure_parts_load hu
  codec_measure_parts_step 76 using code
  codec_measure_parts_step 77 using code
  codec_measure_parts_step 78 using code
  by_cases h : used.toNat + address.toNat < 2 ^ 64
  · have hn : ¬ Udivti3.radix ≤ address.toNat + used.toNat := by dsimp [Udivti3.radix]; omega
    rw [ite_eq_left h] at next
    simpa [addressed, StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using next _
  · have hn : Udivti3.radix ≤ address.toNat + used.toNat := by dsimp [Udivti3.radix]; omega
    rw [ite_eq_right h] at next
    simpa [addressed, StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using next _

theorem rounding_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rdx.toNat + 7 < 2 ^ 64 then base + 360 else base + 1021)) :
    Eventually (step e) P (s, base + 350) := by
  have target := code.targets ("codec_measure_parts_u1021", 1021) (by decide)
  codec_measure_parts_step 79 using code
  codec_measure_parts_step 80 using code
  by_cases h : s.regs.rdx.toNat + 7 < 2 ^ 64
  · have hn : ¬(18446744073709551608 ≤ s.regs.rdx.toNat ∧
        s.regs.rdx.toBitVec ≠ 18446744073709551608#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.rdx.toNat = 18446744073709551608
      omega
    simpa [h, StatusFlags.from_result, hn, flagged, Effects.All] using next _
  · have hn : 18446744073709551608 ≤ s.regs.rdx.toNat ∧
        s.regs.rdx.toBitVec ≠ 18446744073709551608#64 := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.rdx.toNat = 18446744073709551608 at he'
      omega
    simpa [h, StatusFlags.from_result, hn, target, flagged, Effects.All] using next _

theorem alignment_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (aligned s flags,
        if (paddingWord s.regs.rdx.toBitVec).toNat + s.regs.rcx.toNat < 2 ^ 64
        then base + 383 else base + 1021)) :
    Eventually (step e) P (s, base + 360) := by
  have target := code.targets ("codec_measure_parts_u1021", 1021) (by decide)
  have raw : (paddingWord s.regs.rdx.toBitVec).toNat =
      (18446744073709551616 - s.regs.rdx.toNat +
        ((s.regs.rdx.toNat + 7) % 18446744073709551616 &&& 18446744073709551608)) %
          18446744073709551616 := by simp [paddingWord, UintCodec.Arena.paddingWord]
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with
          r13 := UInt64.ofBitVec ((s.regs.rdx.toBitVec + 7#64) &&& ~~~7#64)}
        status := flags}, base + 368) := by
    codec_measure_parts_step 83 using code
    codec_measure_parts_step 84 using code
    codec_measure_parts_step 85 using code
    codec_measure_parts_step 86 using code
    by_cases h : (paddingWord s.regs.rdx.toBitVec).toNat + s.regs.rcx.toNat < 2 ^ 64
    · have hn : ¬ Udivti3.radix ≤ s.regs.rcx.toNat +
          (paddingWord s.regs.rdx.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_left h] at next
      rw [raw] at hn
      simpa [aligned, paddingWord, UintCodec.Arena.paddingWord,
        StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using next _
    · have hn : Udivti3.radix ≤ s.regs.rcx.toNat +
          (paddingWord s.regs.rdx.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_right h] at next
      rw [raw] at hn
      simpa [aligned, paddingWord, UintCodec.Arena.paddingWord,
        StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using next _
  codec_measure_parts_step 81 using code
  codec_measure_parts_step 82 using code
  constructor <;> simpa [BitVec.ofInt_add, BitVec.ofInt_toInt] using rest _

/-- Both LEAs are actual scalar count scaling. The physical Value-slice bound
supplies the omitted product check in reserve_runs; the addition still checks CF. -/
theorem ending_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (ended s flags,
        if (s.regs.rbx.toBitVec * 40).toNat + s.regs.rax.toNat < 2 ^ 64
        then base + 404 else base + 1021)) :
    Eventually (step e) P (s, base + 383) := by
  have target := code.targets ("codec_measure_parts_u1021", 1021) (by decide)
  have scale : s.regs.rbx.toBitVec * 8 + s.regs.rbx.toBitVec * 8 * 4 =
      s.regs.rbx.toBitVec * 40 := by bv_omega
  codec_measure_parts_step 87 using code
  codec_measure_parts_step 88 using code
  codec_measure_parts_step 89 using code
  codec_measure_parts_step 90 using code
  by_cases h : (s.regs.rbx.toBitVec * 40).toNat + s.regs.rax.toNat < 2 ^ 64
  · have hn : ¬ Udivti3.radix ≤ s.regs.rax.toNat + (s.regs.rbx.toBitVec * 40).toNat := by
      dsimp [Udivti3.radix]
      omega
    rw [ite_eq_left h] at next
    simpa [ended, scale, StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using next _
  · have hn : Udivti3.radix ≤ s.regs.rax.toNat + (s.regs.rbx.toBitVec * 40).toNat := by
      dsimp [Udivti3.radix]
      omega
    rw [ite_eq_right h] at next
    simpa [ended, scale, StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using next _

theorem capacity_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (capacity : BitVec 64) (P : MachineState → Prop)
    (loaded : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 8) 8 = some (capacity.toNat : Int))
    (next : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rcx.toNat ≤ capacity.toNat then base + 414 else base + 1021)) :
    Eventually (step e) P (s, base + 404) := by
  have target := code.targets ("codec_measure_parts_u1021", 1021) (by decide)
  codec_measure_parts_step 91 using code
  codec_measure_parts_load loaded
  codec_measure_parts_step 92 using code
  by_cases fits : s.regs.rcx.toNat ≤ capacity.toNat
  · have notAbove : ¬(capacity.toNat ≤ s.regs.rcx.toNat ∧ s.regs.rcx.toBitVec ≠ capacity) := by
      rintro ⟨lower, different⟩
      apply different
      apply BitVec.toNat_inj.mp
      change s.regs.rcx.toNat = capacity.toNat
      omega
    simpa [flagged, fits, StatusFlags.from_result, Udivti3.cf_sub, notAbove, Effects.All] using next _
  · have above : capacity.toNat ≤ s.regs.rcx.toNat ∧ s.regs.rcx.toBitVec ≠ capacity := by
      refine ⟨by omega, ?_⟩
      intro equal
      have same := congrArg BitVec.toNat equal
      change s.regs.rcx.toNat = capacity.toNat at same
      omega
    simpa [flagged, fits, StatusFlags.from_result, Udivti3.cf_sub, above, target, Effects.All] using next _

end SszX86.CodecMeasureParts
