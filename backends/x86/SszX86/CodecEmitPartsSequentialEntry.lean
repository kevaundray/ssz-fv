import SszX86.CodecEmitPartsSteps

namespace SszX86.CodecEmitParts
open Kraken.X64.Parser

/-- Empty values do not inspect Parts, values, or any child plan. -/
theorem sequential_empty_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (empty : s.regs.rcx.toBitVec = 0#64)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rbx := 0}, status := flags}, base + 801)) :
    Eventually (step e) P (s, base + 558) := by
  have target := code.targets ("codec_emit_parts_u711", 711) (by decide)
  codec_parts_step 132 using code
  constructor <;> codec_parts_step 133 using code
  all_goals simp [empty, target, StatusFlags.from_result, Effects.All]
  all_goals codec_parts_step 170 using code
  all_goals constructor
  all_goals codec_parts_step 171 using code
  all_goals simpa only [Effects.All] using next _

def sequentialReady (s : MachineData) (first second : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rcx := UInt64.ofBitVec (s.regs.rcx.toBitVec <<< 4)
    r13 := UInt64.ofBitVec ((s.regs.rcx.toBitVec <<< 4) + (s.regs.rcx.toBitVec <<< 4) * 2)
    rbp := UInt64.ofBitVec (if first = 0 then 0 else first + 16)
    r14 := UInt64.ofBitVec second
    r15 := UInt64.ofBitVec (if first = 0 then s.regs.rsp.toBitVec + 24 else -1)
    rbx := 0}, status := flags}

/-- Actual byte-stride setup and the Parts niche select one of the two fixed
sequential loops. Header observations come from the original immutable Parts. -/
theorem sequential_nonempty_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (first second : BitVec 64) (P : MachineState → Prop)
    (nonempty : s.regs.rcx.toBitVec ≠ 0#64)
    (firstLoad : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (first.toNat : Int))
    (secondLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8) 8 = some (second.toNat : Int))
    (next : ∀ flags, Eventually (step e) P
      (sequentialReady s first second flags, if first = 0 then base + 736 else base + 608)) :
    Eventually (step e) P (s, base + 558) := by
  have target := code.targets ("codec_emit_parts_u715", 715) (by decide)
  codec_parts_step 132 using code
  constructor <;> codec_parts_step 133 using code
  all_goals simp [nonempty, StatusFlags.from_result, Effects.All]
  all_goals codec_parts_step 134 using code
  all_goals simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
    Effects.All, BitVec.take, BitVec.signed]
  all_goals repeat' first | apply And.intro | intro
  all_goals codec_parts_step 135 using code
  all_goals codec_parts_step 136 using code
  all_goals codec_parts_load firstLoad
  all_goals codec_parts_step 137 using code
  all_goals codec_parts_load secondLoad
  all_goals codec_parts_step 138 using code
  all_goals constructor
  all_goals codec_parts_step 139 using code
  all_goals
    by_cases repeated : first = 0#64
    · simp [repeated, target, StatusFlags.from_result, Effects.All]
      codec_parts_step 172 using code
      constructor <;> codec_parts_step 173 using code
      all_goals codec_parts_step 174 using code
      all_goals codec_parts_step 175 using code
      all_goals simpa [sequentialReady, repeated, Effects.All] using next _
    · simp [repeated, StatusFlags.from_result, Effects.All]
      codec_parts_step 140 using code
      codec_parts_step 141 using code
      codec_parts_step 142 using code
      constructor <;> codec_parts_step 143 using code
      all_goals simpa [sequentialReady, repeated, Effects.All] using next _

/-- Arity proves this actual equality-based field exhaustion guard false. -/
theorem sequential_field_guard (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (available : (s.regs.r15.toBitVec + 1).toNat < s.regs.r14.toNat)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r15 := UInt64.ofBitVec (s.regs.r15.toBitVec + 1)},
        status := flags}, base + 620)) :
    Eventually (step e) P (s, base + 608) := by
  have unequal : s.regs.r14.toBitVec - (s.regs.r15.toBitVec + 1) ≠ 0#64 := by
    have bound : (s.regs.r15.toBitVec + 1).toNat < s.regs.r14.toBitVec.toNat := available
    bv_omega
  codec_parts_step 144 using code
  codec_parts_step 145 using code
  codec_parts_step 146 using code
  simpa [unequal, StatusFlags.from_result, Effects.All] using next _

end SszX86.CodecEmitParts
