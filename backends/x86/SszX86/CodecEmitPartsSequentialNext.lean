import SszX86.CodecEmitPartsSequentialArgs

namespace SszX86.CodecEmitParts

def repeatedNextState (s : MachineData) (size : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := 0,
    r12 := UInt64.ofBitVec (s.regs.r12.toBitVec + 48),
    r13 := UInt64.ofBitVec (s.regs.r13.toBitVec - 48),
    rbx := UInt64.ofBitVec (s.regs.rbx.toBitVec + size)}, status := flags}

/-- The returned success status is inspected before the output cursor advances.
The actual byte-count loop decrements by Value's physical stride 48. -/
theorem sequential_repeated_next (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (size : BitVec 64) (P : MachineState → Prop)
    (status : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 88) 4 = some 0)
    (length : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 24) 8 = some (size.toNat : Int))
    (next : ∀ flags, Eventually (step e) P
      (repeatedNextState s size flags,
        if s.regs.r13.toBitVec = 48#64 then base + 801 else base + 736)) :
    Eventually (step e) P (s, base + 778) := by
  have target := code.targets ("codec_emit_parts_u736", 736) (by decide)
  have subtract : s.regs.r13.toBitVec + BitVec.ofInt 64 (-48) = s.regs.r13.toBitVec - 48#64 := by
    bv_omega
  codec_parts_step 186 using code
  codec_parts_load status
  codec_parts_step 187 using code
  constructor <;> codec_parts_step 188 using code
  all_goals simp [StatusFlags.from_result, Effects.All]
  all_goals codec_parts_step 189 using code
  all_goals codec_parts_step 190 using code
  all_goals codec_parts_load length
  all_goals codec_parts_step 191 using code
  all_goals codec_parts_step 192 using code
  all_goals
    by_cases done : s.regs.r13.toBitVec = 48#64
    · simpa [repeatedNextState, subtract, done, target, StatusFlags.from_result, Effects.All] using next _
    · have nonzero : s.regs.r13.toBitVec - 48#64 ≠ 0#64 := by bv_omega
      simpa [repeatedNextState, subtract, done, nonzero, target,
        StatusFlags.from_result, Effects.All] using next _

def fieldNextState (s : MachineData) (size : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := 0,
    r12 := UInt64.ofBitVec (s.regs.r12.toBitVec + 48),
    r13 := UInt64.ofBitVec (s.regs.r13.toBitVec - 48),
    rbp := UInt64.ofBitVec (s.regs.rbp.toBitVec + 24),
    rbx := UInt64.ofBitVec (s.regs.rbx.toBitVec + size)}, status := flags}

/-- A successful fixed field advances the field pointer and value pointer by
their distinct physical strides. No result-padding word is read. -/
theorem sequential_field_next (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (size : BitVec 64) (P : MachineState → Prop)
    (status : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 88) 4 = some 0)
    (length : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 24) 8 = some (size.toNat : Int))
    (next : ∀ flags, Eventually (step e) P
      (fieldNextState s size flags,
        if s.regs.r13.toBitVec = 48#64 then base + 801 else base + 608)) :
    Eventually (step e) P (s, base + 665) := by
  have target := code.targets ("codec_emit_parts_u608", 608) (by decide)
  have subtract : s.regs.r13.toBitVec + BitVec.ofInt 64 (-48) = s.regs.r13.toBitVec - 48#64 := by
    bv_omega
  codec_parts_step 157 using code
  codec_parts_load status
  codec_parts_step 158 using code
  constructor <;> codec_parts_step 159 using code
  all_goals simp [StatusFlags.from_result, Effects.All]
  all_goals codec_parts_step 160 using code
  all_goals codec_parts_step 161 using code
  all_goals codec_parts_step 162 using code
  all_goals codec_parts_step 163 using code
  all_goals codec_parts_load length
  all_goals codec_parts_step 164 using code
  all_goals constructor
  all_goals codec_parts_step 165 using code
  all_goals
    by_cases done : s.regs.r13.toBitVec = 48#64
    · simp [subtract, done, StatusFlags.from_result, Effects.All]
      codec_parts_step 166 using code
      simpa [fieldNextState, subtract, done, Effects.All] using next _
    · have nonzero : s.regs.r13.toBitVec - 48#64 ≠ 0#64 := by bv_omega
      simpa [fieldNextState, subtract, done, nonzero, target,
        StatusFlags.from_result, Effects.All] using next _

end SszX86.CodecEmitParts
