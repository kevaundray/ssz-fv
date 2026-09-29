import SszX86.CodecPlanSingletonImpl
import SszX86.DelimitedReservation
import SszTypedArena

namespace SszX86.CodecPlanSingleton
open Kraken.X64.Parser
open SszX86.UintCodec

macro "codec_plan_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.CodecPlanSingleton.step_at _ _ $hc
     (SszX86.CodecPlanSingleton.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.CodecPlanSingleton.program,
     SszX86.CodecPlanSingleton.programChunk0, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecPlanSingleton.directives, SszX86.CodecPlanSingleton.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "codec_plan_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast])

abbrev paddingWord := UintCodec.Arena.paddingWord

def flagged (s : MachineData) (flags : StatusFlags) : MachineData := {s with status := flags}

def addressed (s : MachineData) (address used : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec address
      r8 := UInt64.ofBitVec used
      r9 := UInt64.ofBitVec (used + address)}
    status := flags}

def aligned (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rcx := UInt64.ofBitVec (paddingWord s.regs.r9.toBitVec + s.regs.r8.toBitVec)}
    status := flags}

def ended (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with
      r8 := UInt64.ofBitVec (s.regs.rcx.toBitVec + 40)}}

structure Header (s : MachineData) (address capacity used : BitVec 64) : Prop where
  address_load : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (used.toNat : Int)

theorem address_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address used : BitVec 64)
    (hb : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (address.toNat : Int))
    (hu : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (used.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (addressed s address used flags,
        if used.toNat + address.toNat < 2^64 then base + 15 else base + 122)) :
    Eventually (step e) P (s, base) := by
  have target := hc.targets ("codec_plan_singleton_u122", 122) (by decide)
  rw [← Int64.add_zero base]
  codec_plan_step 0 using hc
  codec_plan_load hb
  codec_plan_step 1 using hc
  codec_plan_load hu
  codec_plan_step 2 using hc
  codec_plan_step 3 using hc
  codec_plan_step 4 using hc
  by_cases h : used.toNat + address.toNat < 2^64
  · have hn : ¬ Udivti3.radix ≤ address.toNat + used.toNat := by dsimp [Udivti3.radix]; omega
    rw [ite_eq_left h] at next
    simpa [addressed, StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using next _
  · have hn : Udivti3.radix ≤ address.toNat + used.toNat := by dsimp [Udivti3.radix]; omega
    rw [ite_eq_right h] at next
    simpa [addressed, StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using next _

/-- Exact checked address + 7 test, including the last non-overflowing address. -/
theorem rounding_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.r9.toNat + 7 < 2^64 then base + 21 else base + 122)) :
    Eventually (step e) P (s, base + 15) := by
  have target := hc.targets ("codec_plan_singleton_u122", 122) (by decide)
  codec_plan_step 5 using hc
  codec_plan_step 6 using hc
  by_cases h : s.regs.r9.toNat + 7 < 2^64
  · have hn : ¬(18446744073709551608 ≤ s.regs.r9.toNat ∧
        s.regs.r9.toBitVec ≠ 18446744073709551608#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.r9.toNat = 18446744073709551608
      omega
    simpa [h, StatusFlags.from_result, hn, flagged, Effects.All] using next _
  · have hn : 18446744073709551608 ≤ s.regs.r9.toNat ∧
        s.regs.r9.toBitVec ≠ 18446744073709551608#64 := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.r9.toNat = 18446744073709551608 at he'
      omega
    simpa [h, StatusFlags.from_result, hn, target, flagged, Effects.All] using next _

theorem alignment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (aligned s flags,
        if (paddingWord s.regs.r9.toBitVec).toNat + s.regs.r8.toNat < 2^64
        then base + 37 else base + 122)) :
    Eventually (step e) P (s, base + 21) := by
  have target := hc.targets ("codec_plan_singleton_u122", 122) (by decide)
  have raw : (paddingWord s.regs.r9.toBitVec).toNat =
      (18446744073709551616 - s.regs.r9.toNat +
        ((s.regs.r9.toNat + 7) % 18446744073709551616 &&& 18446744073709551608)) %
          18446744073709551616 := by simp [paddingWord, UintCodec.Arena.paddingWord]
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with
          rcx := UInt64.ofBitVec ((s.regs.r9.toBitVec + 7#64) &&& ~~~7#64)}
        status := flags}, base + 29) := by
    codec_plan_step 9 using hc
    codec_plan_step 10 using hc
    codec_plan_step 11 using hc
    by_cases h : (paddingWord s.regs.r9.toBitVec).toNat + s.regs.r8.toNat < 2^64
    · have hn : ¬ Udivti3.radix ≤ s.regs.r8.toNat +
          (paddingWord s.regs.r9.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_left h] at next
      rw [raw] at hn
      simpa [aligned, paddingWord, UintCodec.Arena.paddingWord,
        StatusFlags.from_result, hn, Effects.All, UInt64.add_comm] using next _
    · have hn : Udivti3.radix ≤ s.regs.r8.toNat +
          (paddingWord s.regs.r9.toBitVec).toNat := by dsimp [Udivti3.radix]; omega
      rw [ite_eq_right h] at next
      rw [raw] at hn
      simpa [aligned, paddingWord, UintCodec.Arena.paddingWord,
        StatusFlags.from_result, hn, target, Effects.All, UInt64.add_comm] using next _
  codec_plan_step 7 using hc
  codec_plan_step 8 using hc
  constructor <;> simpa [BitVec.ofInt_add, BitVec.ofInt_toInt] using rest _

/-- The literal -41 threshold is exactly checked addition of one 40-byte Plan. -/
theorem end_guard_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (flagged s flags, if s.regs.rcx.toNat + 40 < 2^64 then base + 43 else base + 122)) :
    Eventually (step e) P (s, base + 37) := by
  have target := hc.targets ("codec_plan_singleton_u122", 122) (by decide)
  codec_plan_step 12 using hc
  codec_plan_step 13 using hc
  by_cases h : s.regs.rcx.toNat + 40 < 2^64
  · have hn : ¬(18446744073709551575 ≤ s.regs.rcx.toNat ∧
        s.regs.rcx.toBitVec ≠ 18446744073709551575#64) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      change s.regs.rcx.toNat = 18446744073709551575
      omega
    simpa [h, StatusFlags.from_result, hn, flagged, Effects.All] using next _
  · have hn : 18446744073709551575 ≤ s.regs.rcx.toNat ∧
        s.regs.rcx.toBitVec ≠ 18446744073709551575#64 := by
      refine ⟨by omega, ?_⟩
      intro he
      have he' := congrArg BitVec.toNat he
      change s.regs.rcx.toNat = 18446744073709551575 at he'
      omega
    simpa [h, StatusFlags.from_result, hn, target, flagged, Effects.All] using next _

theorem capacity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (capacity : BitVec 64)
    (hl : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (capacity.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (flagged (ended s) flags,
        if (s.regs.rcx.toBitVec + 40#64).toNat ≤ capacity.toNat then base + 53 else base + 122)) :
    Eventually (step e) P (s, base + 43) := by
  have target := hc.targets ("codec_plan_singleton_u122", 122) (by decide)
  have raw : (s.regs.rcx.toBitVec + 40#64).toNat =
      (s.regs.rcx.toNat + 40) % 18446744073709551616 := by simp
  codec_plan_step 14 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  codec_plan_step 15 using hc
  codec_plan_load hl
  codec_plan_step 16 using hc
  by_cases h : (s.regs.rcx.toBitVec + 40#64).toNat ≤ capacity.toNat
  · have hn : ¬(capacity.toNat ≤ (s.regs.rcx.toBitVec + 40#64).toNat ∧
        s.regs.rcx.toBitVec + 40#64 ≠ capacity) := by
      rintro ⟨hle, hne⟩
      apply hne
      apply BitVec.toNat_inj.mp
      omega
    rw [ite_eq_left h] at next
    rw [raw] at hn
    simpa [StatusFlags.from_result, hn, ended, flagged, Effects.All] using next _
  · have hn : capacity.toNat ≤ (s.regs.rcx.toBitVec + 40#64).toNat ∧
        s.regs.rcx.toBitVec + 40#64 ≠ capacity := by
      refine ⟨by omega, ?_⟩
      intro he
      rw [he] at h
      exact h (Nat.le_refl _)
    rw [ite_eq_right h] at next
    rw [raw] at hn
    simpa [StatusFlags.from_result, hn, target, ended, flagged, Effects.All] using next _

end SszX86.CodecPlanSingleton
