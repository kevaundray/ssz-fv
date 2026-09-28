import SszX86.BitVectorCore

namespace SszX86.BitVector

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def addStatusState (s : MachineData) (statusWord : BitVec 32) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec (statusWord.setWidth 64)}, status := flags}

theorem add_status_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (statusWord : BitVec 32)
    (hl : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 80#64) 4 = some (statusWord.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (addStatusState s statusWord flags,
        if statusWord = 0#32 then base + 4592 else base + 1776)) :
    Eventually (step e) P (s, base + 1764) := by
  have target := hc.targets ("bitVector_u4592", 4592) (by decide)
  bitvector_step 52 using hc
  bitvector_load hl
  bitvector_step 53 using hc
  constructor <;> bitvector_step 54 using hc
  all_goals
    by_cases zero : statusWord = 0#32
    · simpa [zero, target, addStatusState, StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, target, addStatusState, StatusFlags.from_result, Effects.All] using next _

/-- Scope's status is checked before the body can read a tail byte. -/
theorem exact_status_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (statusWord : BitVec 32)
    (hl : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 80#64) 4 = some (statusWord.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if statusWord = 0#32 then base + 4832 else base + 4650)) :
    Eventually (step e) P (s, base + 4639) := by
  have target := hc.targets ("bitVector_u4832", 4832) (by decide)
  bitvector_step 94 using hc
  bitvector_load hl
  bitvector_step 95 using hc
  by_cases zero : statusWord = 0#32
  · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _
  · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _

theorem nonzero_byte (value : BitVec 64) :
    BitVec.ofNat 8 (!(value == 0#64)).toNat =
      (if value = 0#64 then 0#8 else 1#8) := by
  by_cases zero : value = 0#64
  · simp [zero]
  · simp [zero, beq_eq_false_iff_ne.mpr zero]

def paddingGateState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (s.regs.rax.toBitVec.replaceLow
        (if s.regs.r13.toBitVec = 0#64 then 0#8 else 1#8))
      rcx := UInt64.ofBitVec (s.regs.rcx.toBitVec.replaceLow
        (if s.regs.r14.toBitVec = 0#64 then 0#8 else 1#8))}
    status := flags}

/-- Empty inputs and exact multiples of eight bypass the native tail-byte read. -/
theorem padding_gate_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (paddingGateState s flags,
        if s.regs.r13.toBitVec = 0#64 ∨ s.regs.r14.toBitVec = 0#64
          then base + 5233 else base + 4852)) :
    Eventually (step e) P (s, base + 4832) := by
  have target := hc.targets ("bitVector_u5233", 5233) (by decide)
  have byteProjection (value : BitVec 64) (byte : BitVec 8) :
      (value.extractLsb' 8 56 ++ byte).setWidth 8 = byte :=
    @BitVec.setWidth_append_eq_right 56 8 (value.extractLsb' 8 56) byte
  have aZero := byteProjection s.regs.rax.toBitVec 0#8
  have aOne := byteProjection s.regs.rax.toBitVec 1#8
  have cZero := byteProjection s.regs.rcx.toBitVec 0#8
  have cOne := byteProjection s.regs.rcx.toBitVec 1#8
  bitvector_step 143 using hc
  constructor <;> bitvector_step 144 using hc
  all_goals bitvector_step 145 using hc
  all_goals constructor <;> bitvector_step 146 using hc
  all_goals bitvector_step 147 using hc
  all_goals constructor <;> bitvector_step 148 using hc
  all_goals
    by_cases remainderZero : s.regs.r13.toBitVec = 0#64 <;>
      by_cases lengthZero : s.regs.r14.toBitVec = 0#64 <;>
      simpa [paddingGateState, remainderZero, lengthZero, target,
        StatusFlags.from_result, Effects.All, BitVec.replaceLow, BitVec.drop,
        nonzero_byte, aZero, aOne, cZero, cOne] using next _

end SszX86.BitVector
