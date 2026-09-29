import SszX86.CodecMeasureUnionCompare

namespace SszX86.CodecMeasure
open SszNative BoolCodec UintCodec

/-- The byte iterator tests exhaustion before loading a Variant. -/
theorem union_scan_guard (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rbp.toBitVec = 0 then base + 1168 else base + 233)) :
    Eventually (step e) P (s, base + 224) := by
  have target := code.targets ("measure_u1168", 1168) (by decide)
  codec_measure_step 0 row 54 using code
  constructor <;> codec_measure_step 0 row 55 using code
  all_goals
    by_cases empty : s.regs.rbp.toBitVec = 0
    · simpa [StatusFlags.from_result, empty, target, Effects.All] using next _
    · simpa [StatusFlags.from_result, empty, Effects.All] using next _

def unionCompareState (s : MachineData) (chosen : NatOperand) : MachineData :=
  {s with regs := {s.regs with
    rdi := UInt64.ofBitVec chosen.pointer, rsi := UInt64.ofBitVec chosen.payload,
    rdx := s.regs.r12, rcx := s.regs.r13}}

/-- Variant.selector is at byte8 of the current Variant, and the iterator keeps
R15 one 24-byte slot behind until after comparison. -/
theorem union_compare_prepare (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (chosen : NatOperand) (P : MachineState → Prop)
    (pointer : Mem.loadInt s.dmem (s.regs.r15.toBitVec + 32) 8 =
      some (chosen.pointer.toNat : Int))
    (payload : Mem.loadInt s.dmem (s.regs.r15.toBitVec + 40) 8 =
      some (chosen.payload.toNat : Int))
    (next : Eventually (step e) P (unionCompareState s chosen, base + 247)) :
    Eventually (step e) P (s, base + 233) := by
  codec_measure_step 0 row 56 using code
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, pointer, Delimited.word_cast]
  codec_measure_step 0 row 57 using code
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, payload, Delimited.word_cast]
  codec_measure_step 0 row 58 using code
  codec_measure_step 0 row 59 using code
  simpa [unionCompareState] using next

def unionAdvanced (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    r15 := UInt64.ofBitVec (s.regs.r15.toBitVec + 24),
    rbp := UInt64.ofBitVec (s.regs.rbp.toBitVec - 24)}, status := flags}

/-- After exactly one numerical comparison, the actual code either chooses that
Variant immediately or advances once. No later equal selector can preempt it. -/
theorem union_scan_advance (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (unionAdvanced s flags,
        if s.regs.rax.toBitVec.setWidth 8 = 0 then base + 264 else base + 224)) :
    Eventually (step e) P (s, base + 252) := by
  have target := code.targets ("measure_u224", 224) (by decide)
  codec_measure_step 0 row 61 using code
  codec_measure_step 0 row 62 using code
  codec_measure_step 0 row 63 using code
  constructor <;> codec_measure_step 1 row 0 using code
  all_goals
    by_cases equal : s.regs.rax.toBitVec.setWidth 8 = 0
    · simpa [unionAdvanced, StatusFlags.from_result, equal, Effects.All,
        BitVec.sub_eq_add_neg] using next _
    · simpa [unionAdvanced, StatusFlags.from_result, equal, target, Effects.All,
        BitVec.sub_eq_add_neg] using next _

end SszX86.CodecMeasure
