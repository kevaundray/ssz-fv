import SszX86.CodecMeasureFixedVector
import SszX86.CodecMeasureFixedArithmeticAdd

namespace SszX86.CodecMeasureFixed
open BoolCodec UintCodec

def fieldReady (s : MachineData) (fields child : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec fields,
    rsi := UInt64.ofBitVec child, rdi := s.regs.r13, rdx := s.regs.r12}}

theorem field_prepare (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (fields child : BitVec 64) (P : MachineState → Prop)
    (fieldsLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 80) 8 = some (fields.toNat : Int))
    (childLoad : Mem.loadInt s.dmem (fields + s.regs.rbp.toBitVec + 16) 8 = some (child.toNat : Int))
    (next : Eventually (step e) P (fieldReady s fields child, base + 144)) :
    Eventually (step e) P (s, base + 128) := by
  codec_measure_fixed_step 34 using hc
  codec_measure_fixed_load fieldsLoad
  codec_measure_fixed_step 35 using hc
  codec_measure_fixed_load childLoad
  codec_measure_fixed_step 36 using hc
  codec_measure_fixed_step 37 using hc
  simpa [fieldReady] using next

theorem field_call (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (slot : ArithmeticCallSlot s)
    (next : Eventually (step e) P (arithmeticCallState s (base + 149).toBitVec, base)) :
    Eventually (step e) P (s, base + 144) := by
  codec_measure_fixed_step 38 using hc
  apply Delimited.store_cps
  · exact slot
  · simpa [arithmeticCallState, NatDivision.callState, Effects.All, Int64.add_assoc] using next

def fieldResult (s : MachineData) (status : BitVec 32) (option pointer payload : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec (status.setWidth 64),
    rdx := UInt64.ofBitVec option, rcx := UInt64.ofBitVec pointer, r8 := UInt64.ofBitVec payload}}

theorem field_result_loads (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (status : BitVec 32) (option pointer payload : BitVec 64)
    (P : MachineState → Prop)
    (statusLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 64) 4 = some (status.toNat : Int))
    (optionLoad : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (option.toNat : Int))
    (pointerLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8) 8 = some (pointer.toNat : Int))
    (payloadLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16) 8 = some (payload.toNat : Int))
    (next : Eventually (step e) P (fieldResult s status option pointer payload, base + 167)) :
    Eventually (step e) P (s, base + 149) := by
  have statusCast : BitVec.ofInt 32 (status.toNat : Int) = status := by bv_omega
  codec_measure_fixed_step 39 using hc
  simp only [MachineData.load, Effects.All, statusLoad, statusCast,
    show Width.W32.bytes = 4 by rfl, show Width.W32.bits = 32 by rfl]
  codec_measure_fixed_step 40 using hc
  codec_measure_fixed_load optionLoad
  codec_measure_fixed_step 41 using hc
  codec_measure_fixed_load pointerLoad
  codec_measure_fixed_step 42 using hc
  codec_measure_fixed_load payloadLoad
  simpa [fieldResult] using next

theorem field_status (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags},
      if s.regs.rax.toBitVec.setWidth 32 = 0 then base + 175 else base + 709)) :
    Eventually (step e) P (s, base + 167) := by
  have target := hc.targets ("codec_measure_fixed_u709", 709) (by decide)
  codec_measure_fixed_step 43 using hc
  constructor <;> codec_measure_fixed_step 44 using hc
  all_goals
    by_cases success : s.regs.rax.toBitVec.setWidth 32 = 0
    · simpa [StatusFlags.from_result, success, Effects.All] using next _
    · simpa [StatusFlags.from_result, success, target, Effects.All] using next _

theorem field_option (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags},
      if s.regs.rdx.toBitVec.setWidth 8 &&& 1#8 = 0 then base + 680 else base + 184)) :
    Eventually (step e) P (s, base + 175) := by
  have target := hc.targets ("codec_measure_fixed_u680", 680) (by decide)
  codec_measure_fixed_step 45 using hc
  constructor <;> codec_measure_fixed_step 46 using hc
  all_goals
    by_cases absent : s.regs.rdx.toBitVec.setWidth 8 &&& 1#8 = 0
    · simpa [StatusFlags.from_result, absent, target, Effects.All] using next _
    · simpa [StatusFlags.from_result, absent, Effects.All] using next _

def fieldAddReady (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rdi := s.regs.r13, rsi := s.regs.r14,
    rdx := s.regs.r15, r9 := s.regs.r12}}

theorem field_add_prepare (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (fieldAddReady s, base + 196)) :
    Eventually (step e) P (s, base + 184) := by
  codec_measure_fixed_step 47 using hc
  codec_measure_fixed_step 48 using hc
  codec_measure_fixed_step 49 using hc
  codec_measure_fixed_step 50 using hc
  simpa [fieldAddReady] using next

def fieldSum (s : MachineData) (status : BitVec 32) (pointer payload : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec (status.setWidth 64),
    r14 := UInt64.ofBitVec pointer, r15 := UInt64.ofBitVec payload}}

theorem field_sum_loads (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (status : BitVec 32) (pointer payload : BitVec 64)
    (P : MachineState → Prop)
    (statusLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 64) 4 = some (status.toNat : Int))
    (pointerLoad : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (pointer.toNat : Int))
    (payloadLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8) 8 = some (payload.toNat : Int))
    (next : Eventually (step e) P (fieldSum s status pointer payload, base + 214)) :
    Eventually (step e) P (s, base + 201) := by
  have statusCast : BitVec.ofInt 32 (status.toNat : Int) = status := by bv_omega
  codec_measure_fixed_step 52 using hc
  simp only [MachineData.load, Effects.All, statusLoad, statusCast,
    show Width.W32.bytes = 4 by rfl, show Width.W32.bits = 32 by rfl]
  codec_measure_fixed_step 53 using hc
  codec_measure_fixed_load pointerLoad
  codec_measure_fixed_step 54 using hc
  codec_measure_fixed_load payloadLoad
  simpa [fieldSum] using next

theorem field_sum_status (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags},
      if s.regs.rax.toBitVec.setWidth 32 = 0 then base + 222 else base + 607)) :
    Eventually (step e) P (s, base + 214) := by
  have target := hc.targets ("codec_measure_fixed_u607", 607) (by decide)
  codec_measure_fixed_step 55 using hc
  constructor <;> codec_measure_fixed_step 56 using hc
  all_goals
    by_cases success : s.regs.rax.toBitVec.setWidth 32 = 0
    · simpa [StatusFlags.from_result, success, Effects.All] using next _
    · simpa [StatusFlags.from_result, success, target, Effects.All] using next _

def fieldAdvanced (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rbp := UInt64.ofBitVec (s.regs.rbp.toBitVec + 24)}, status := flags}

theorem field_advance (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (fieldAdvanced s flags, base + 226)) :
    Eventually (step e) P (s, base + 222) := by
  codec_measure_fixed_step 57 using hc
  simpa [fieldAdvanced] using next _

theorem field_backedge (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (extent : BitVec 64) (P : MachineState → Prop)
    (extentLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 72) 8 = some (extent.toNat : Int))
    (next : ∀ flags, Eventually (step e) P ({s with status := flags},
      if extent = s.regs.rbp.toBitVec then base + 271 else base + 128)) :
    Eventually (step e) P (s, base + 226) := by
  have target := hc.targets ("codec_measure_fixed_u128", 128) (by decide)
  have difference : (extent - s.regs.rbp.toBitVec = 0) ↔ extent = s.regs.rbp.toBitVec := by bv_omega
  codec_measure_fixed_step 58 using hc
  codec_measure_fixed_load extentLoad
  codec_measure_fixed_step 59 using hc
  by_cases done : extent = s.regs.rbp.toBitVec
  · simp [StatusFlags.from_result, done, Effects.All]
    codec_measure_fixed_step 60 using hc
    simpa [done] using next _
  · simpa [StatusFlags.from_result, difference, done, target, Effects.All] using next _

end SszX86.CodecMeasureFixed
