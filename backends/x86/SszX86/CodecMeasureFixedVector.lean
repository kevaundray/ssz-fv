import SszX86.CodecMeasureFixedControl
import SszX86.CodecMeasureFixedArithmeticCall

namespace SszX86.CodecMeasureFixed
open BoolCodec UintCodec

def vectorReady (s : MachineData) (child : BitVec 64) : MachineData :=
  {s with regs := {s.regs with
    r14 := s.regs.rsi
    rsi := UInt64.ofBitVec child
    rdi := s.regs.rsp
    rdx := s.regs.r12}}

theorem vector_prepare (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (child : BitVec 64) (P : MachineState → Prop)
    (pointer : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 24) 8 = some (child.toNat : Int))
    (next : Eventually (step e) P (vectorReady s child, base + 428)) :
    Eventually (step e) P (s, base + 415) := by
  codec_measure_fixed_step 104 using hc
  codec_measure_fixed_step 105 using hc
  codec_measure_fixed_load pointer
  codec_measure_fixed_step 106 using hc
  codec_measure_fixed_step 107 using hc
  simpa [vectorReady] using next

/-- Actual self-CALL: width zero does not bypass the child measurement. -/
theorem vector_call (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (slot : ArithmeticCallSlot s)
    (next : Eventually (step e) P (arithmeticCallState s (base + 433).toBitVec, base)) :
    Eventually (step e) P (s, base + 428) := by
  codec_measure_fixed_step 108 using hc
  apply Delimited.store_cps
  · exact slot
  · simpa [arithmeticCallState, NatDivision.callState, Effects.All, Int64.add_assoc] using next

def vectorResult (s : MachineData) (status : BitVec 32) (option pointer payload : BitVec 64) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec (status.setWidth 64)
    rcx := UInt64.ofBitVec option
    rsi := UInt64.ofBitVec pointer
    rdx := UInt64.ofBitVec payload}}

/-- All result loads precede the status branch, including inactive/padding
words. Mapping, not a semantic initialization assertion, justifies those loads. -/
theorem vector_result_loads (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (status : BitVec 32) (option pointer payload : BitVec 64)
    (P : MachineState → Prop)
    (statusLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 64) 4 = some (status.toNat : Int))
    (optionLoad : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (option.toNat : Int))
    (pointerLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8) 8 = some (pointer.toNat : Int))
    (payloadLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16) 8 = some (payload.toNat : Int))
    (next : Eventually (step e) P (vectorResult s status option pointer payload, base + 451)) :
    Eventually (step e) P (s, base + 433) := by
  have statusCast : BitVec.ofInt 32 (status.toNat : Int) = status := by bv_omega
  codec_measure_fixed_step 109 using hc
  simp only [MachineData.load, Effects.All, statusLoad, statusCast,
    show Width.W32.bytes = 4 by rfl, show Width.W32.bits = 32 by rfl]
  codec_measure_fixed_step 110 using hc
  codec_measure_fixed_load optionLoad
  codec_measure_fixed_step 111 using hc
  codec_measure_fixed_load pointerLoad
  codec_measure_fixed_step 112 using hc
  codec_measure_fixed_load payloadLoad
  simpa [vectorResult] using next

theorem vector_status (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rax.toBitVec.setWidth 32 = 0 then base + 562 else base + 455)) :
    Eventually (step e) P (s, base + 451) := by
  have target := hc.targets ("codec_measure_fixed_u562", 562) (by decide)
  codec_measure_fixed_step 113 using hc
  constructor <;> codec_measure_fixed_step 114 using hc
  all_goals
    by_cases success : s.regs.rax.toBitVec.setWidth 32 = 0
    · simpa [StatusFlags.from_result, success, target, Effects.All] using next _
    · simpa [StatusFlags.from_result, success, Effects.All] using next _

theorem vector_option (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags},
        if s.regs.rcx.toBitVec.setWidth 8 &&& 1#8 = 0 then base + 680 else base + 567)) :
    Eventually (step e) P (s, base + 562) := by
  have target := hc.targets ("codec_measure_fixed_u680", 680) (by decide)
  codec_measure_fixed_step 142 using hc
  constructor <;> codec_measure_fixed_step 143 using hc
  all_goals
    by_cases absent : s.regs.rcx.toBitVec.setWidth 8 &&& 1#8 = 0
    · simpa [StatusFlags.from_result, absent, target, Effects.All] using next _
    · simpa [StatusFlags.from_result, absent, Effects.All] using next _

def multiplyReady (s : MachineData) (pointer payload : BitVec 64) : MachineData :=
  {s with regs := {s.regs with
    rcx := UInt64.ofBitVec pointer
    r8 := UInt64.ofBitVec payload
    rdi := s.regs.rsp
    r9 := s.regs.r12}}

theorem multiply_prepare (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64) (P : MachineState → Prop)
    (pointerLoad : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 8) 8 = some (pointer.toNat : Int))
    (payloadLoad : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 16) 8 = some (payload.toNat : Int))
    (next : Eventually (step e) P (multiplyReady s pointer payload, base + 581)) :
    Eventually (step e) P (s, base + 567) := by
  codec_measure_fixed_step 144 using hc
  codec_measure_fixed_load pointerLoad
  codec_measure_fixed_step 145 using hc
  codec_measure_fixed_load payloadLoad
  codec_measure_fixed_step 146 using hc
  codec_measure_fixed_step 147 using hc
  simpa [multiplyReady] using next

end SszX86.CodecMeasureFixed
