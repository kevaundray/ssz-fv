import SszX86.CodecMeasureFixedVector

namespace SszX86.CodecMeasureFixed
open BoolCodec UintCodec

def divideReady (s : MachineData) (pointer payload : BitVec 64) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec pointer
    rdx := UInt64.ofBitVec payload
    rdi := s.regs.rsp
    rcx := 8
    rsi := UInt64.ofBitVec pointer
    r8 := s.regs.r12}}

/-- Bit-vector width always invokes quotient/remainder first, even for a small
logical length; no logical-Nat bound is imposed at the callsite. -/
theorem divide_prepare (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64) (P : MachineState → Prop)
    (pointerLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8) 8 = some (pointer.toNat : Int))
    (payloadLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16) 8 = some (payload.toNat : Int))
    (next : Eventually (step e) P (divideReady s pointer payload, base + 313)) :
    Eventually (step e) P (s, base + 291) := by
  codec_measure_fixed_step 74 using hc
  codec_measure_fixed_load pointerLoad
  codec_measure_fixed_step 75 using hc
  codec_measure_fixed_load payloadLoad
  codec_measure_fixed_step 76 using hc
  codec_measure_fixed_step 77 using hc
  codec_measure_fixed_step 78 using hc
  codec_measure_fixed_step 79 using hc
  simpa [divideReady] using next

def divideResult (s : MachineData) (status : BitVec 32)
    (pointer payload remainder : BitVec 64) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec (status.setWidth 64)
    r14 := UInt64.ofBitVec pointer
    r15 := UInt64.ofBitVec payload
    rcx := UInt64.ofBitVec remainder}}

theorem divide_result_loads (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (status : BitVec 32) (pointer payload remainder : BitVec 64)
    (P : MachineState → Prop)
    (statusLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 64) 4 = some (status.toNat : Int))
    (pointerLoad : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (pointer.toNat : Int))
    (payloadLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8) 8 = some (payload.toNat : Int))
    (remainderLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16) 8 = some (remainder.toNat : Int))
    (next : Eventually (step e) P (divideResult s status pointer payload remainder, base + 336)) :
    Eventually (step e) P (s, base + 318) := by
  have statusCast : BitVec.ofInt 32 (status.toNat : Int) = status := by bv_omega
  codec_measure_fixed_step 81 using hc
  simp only [MachineData.load, Effects.All, statusLoad, statusCast,
    show Width.W32.bytes = 4 by rfl, show Width.W32.bits = 32 by rfl]
  codec_measure_fixed_step 82 using hc
  codec_measure_fixed_load pointerLoad
  codec_measure_fixed_step 83 using hc
  codec_measure_fixed_load payloadLoad
  codec_measure_fixed_step 84 using hc
  codec_measure_fixed_load remainderLoad
  simpa [divideResult] using next

theorem divide_status (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rax.toBitVec.setWidth 32 = 0 then base + 526 else base + 344)) :
    Eventually (step e) P (s, base + 336) := by
  have target := hc.targets ("codec_measure_fixed_u526", 526) (by decide)
  codec_measure_fixed_step 85 using hc
  constructor <;> codec_measure_fixed_step 86 using hc
  all_goals
    by_cases success : s.regs.rax.toBitVec.setWidth 32 = 0
    · simpa [StatusFlags.from_result, success, target, Effects.All] using next _
    · simpa [StatusFlags.from_result, success, Effects.All] using next _

theorem remainder_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rcx.toBitVec = 0 then base + 271 else base + 535)) :
    Eventually (step e) P (s, base + 526) := by
  have target := hc.targets ("codec_measure_fixed_u271", 271) (by decide)
  codec_measure_fixed_step 132 using hc
  constructor <;> codec_measure_fixed_step 133 using hc
  all_goals
    by_cases divisible : s.regs.rcx.toBitVec = 0
    · simpa [StatusFlags.from_result, divisible, target, Effects.All] using next _
    · simpa [StatusFlags.from_result, divisible, Effects.All] using next _

def roundedReady (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdi := s.regs.rsp
      r8 := 1
      rsi := s.regs.r14
      rdx := s.regs.r15
      rcx := 0
      r9 := s.regs.r12}
    status := flags}

theorem round_prepare (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (roundedReady s flags, base + 555)) :
    Eventually (step e) P (s, base + 535) := by
  codec_measure_fixed_step 134 using hc
  codec_measure_fixed_step 135 using hc
  codec_measure_fixed_step 136 using hc
  codec_measure_fixed_step 137 using hc
  codec_measure_fixed_step 138 using hc
  constructor <;> codec_measure_fixed_step 139 using hc
  all_goals simpa [roundedReady] using next _

theorem rounded_jump (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (s, base + 586)) :
    Eventually (step e) P (s, base + 560) := by
  codec_measure_fixed_step 141 using hc
  simpa [Int64.add_assoc] using next

def arithmeticResult (s : MachineData) (status : BitVec 32) (pointer payload : BitVec 64) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec (status.setWidth 64)
    r14 := UInt64.ofBitVec pointer
    r15 := UInt64.ofBitVec payload}}

theorem arithmetic_result_loads (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (status : BitVec 32) (pointer payload : BitVec 64)
    (P : MachineState → Prop)
    (statusLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 64) 4 = some (status.toNat : Int))
    (pointerLoad : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (pointer.toNat : Int))
    (payloadLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8) 8 = some (payload.toNat : Int))
    (next : Eventually (step e) P (arithmeticResult s status pointer payload, base + 599)) :
    Eventually (step e) P (s, base + 586) := by
  have statusCast : BitVec.ofInt 32 (status.toNat : Int) = status := by bv_omega
  codec_measure_fixed_step 149 using hc
  simp only [MachineData.load, Effects.All, statusLoad, statusCast,
    show Width.W32.bytes = 4 by rfl, show Width.W32.bits = 32 by rfl]
  codec_measure_fixed_step 150 using hc
  codec_measure_fixed_load pointerLoad
  codec_measure_fixed_step 151 using hc
  codec_measure_fixed_load payloadLoad
  simpa [arithmeticResult] using next

theorem arithmetic_status (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rax.toBitVec.setWidth 32 = 0 then base + 271 else base + 607)) :
    Eventually (step e) P (s, base + 599) := by
  have target := hc.targets ("codec_measure_fixed_u271", 271) (by decide)
  codec_measure_fixed_step 152 using hc
  constructor <;> codec_measure_fixed_step 153 using hc
  all_goals
    by_cases success : s.regs.rax.toBitVec.setWidth 32 = 0
    · simpa [StatusFlags.from_result, success, target, Effects.All] using next _
    · simpa [StatusFlags.from_result, success, Effects.All] using next _

end SszX86.CodecMeasureFixed
