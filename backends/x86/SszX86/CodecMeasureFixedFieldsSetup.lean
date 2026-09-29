import SszX86.CodecMeasureFixedFields

namespace SszX86.CodecMeasureFixed
open BoolCodec UintCodec
open Kraken.X64

def fieldsSelected (s : MachineData) (offset count : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec offset, rcx := UInt64.ofBitVec count}}

theorem container_fields (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : BitVec 64) (P : MachineState → Prop)
    (countLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16) 8 = some (count.toNat : Int))
    (next : ∀ flags, Eventually (step e) P ({fieldsSelected s 8 count with status := flags},
      if count = 0 then base + 254 else base + 81)) :
    Eventually (step e) P (s, base + 62) := by
  have target := hc.targets ("codec_measure_fixed_u254", 254) (by decide)
  codec_measure_fixed_step 19 using hc
  codec_measure_fixed_step 20 using hc
  codec_measure_fixed_load countLoad
  codec_measure_fixed_step 21 using hc
  constructor <;> codec_measure_fixed_step 22 using hc
  all_goals
    by_cases empty : count = 0
    · simpa [fieldsSelected, StatusFlags.from_result, empty, target, Effects.All] using next _
    · simpa [fieldsSelected, StatusFlags.from_result, empty, Effects.All] using next _

theorem progressive_container_fields (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : BitVec 64) (P : MachineState → Prop)
    (countLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 32) 8 = some (count.toNat : Int))
    (next : ∀ flags, Eventually (step e) P ({fieldsSelected s 24 count with status := flags},
      if count = 0 then base + 254 else base + 81)) :
    Eventually (step e) P (s, base + 235) := by
  have target := hc.targets ("codec_measure_fixed_u81", 81) (by decide)
  codec_measure_fixed_step 61 using hc
  codec_measure_fixed_step 62 using hc
  codec_measure_fixed_load countLoad
  codec_measure_fixed_step 63 using hc
  constructor <;> codec_measure_fixed_step 64 using hc
  all_goals
    by_cases empty : count = 0
    · simpa [fieldsSelected, StatusFlags.from_result, empty, Effects.All] using next _
    · simpa [fieldsSelected, StatusFlags.from_result, empty, target, Effects.All] using next _

def fieldsPointer (s : MachineData) (pointer : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec pointer}}

theorem fields_pointer_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer : BitVec 64) (P : MachineState → Prop)
    (pointerLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + s.regs.rax.toBitVec) 8 = some (pointer.toNat : Int))
    (next : Eventually (step e) P (fieldsPointer s pointer, base + 85)) :
    Eventually (step e) P (s, base + 81) := by
  codec_measure_fixed_step 23 using hc
  codec_measure_fixed_load pointerLoad
  simpa [fieldsPointer] using next

def fieldsPointerSaved (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 80) 8 s.regs.rax.toBitVec.toInt}

theorem fields_pointer_save (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 80) 8 = some old)
    (next : Eventually (step e) P (fieldsPointerSaved s, base + 90)) :
    Eventually (step e) P (s, base + 85) := by
  codec_measure_fixed_step 24 using hc
  apply Delimited.store_cps
  · exact slot
  · simpa [fieldsPointerSaved, Effects.All] using next

def fieldsShifted (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rcx := UInt64.ofBitVec (s.regs.rcx.toBitVec <<< 3)}, status := flags}

theorem fields_shift (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (fieldsShifted s flags, base + 94)) :
    Eventually (step e) P (s, base + 90) := by
  codec_measure_fixed_step 25 using hc
  simp (config := {instances := true}) [ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
    BitVec.take, Effects.All]
  repeat' first | apply And.intro | intro
  all_goals simpa [fieldsShifted] using next _

def fieldsExtent (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec (s.regs.rcx.toBitVec + s.regs.rcx.toBitVec * 2)}}

theorem fields_extent (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (fieldsExtent s, base + 98)) :
    Eventually (step e) P (s, base + 94) := by
  codec_measure_fixed_step 26 using hc
  simpa [fieldsExtent] using next

def fieldsExtentSaved (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 72) 8 s.regs.rax.toBitVec.toInt}

theorem fields_extent_save (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 72) 8 = some old)
    (next : Eventually (step e) P (fieldsExtentSaved s, base + 103)) :
    Eventually (step e) P (s, base + 98) := by
  codec_measure_fixed_step 27 using hc
  apply Delimited.store_cps
  · exact slot
  · simpa [fieldsExtentSaved, Effects.All] using next

def fieldsLoop (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rbp := 0, r13 := s.regs.rsp, r14 := 0, r15 := 0}, status := flags}

theorem fields_loop_init (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (fieldsLoop s flags, base + 128)) :
    Eventually (step e) P (s, base + 103) := by
  codec_measure_fixed_step 28 using hc
  constructor <;> codec_measure_fixed_step 29 using hc
  all_goals codec_measure_fixed_step 30 using hc
  all_goals constructor <;> codec_measure_fixed_step 31 using hc
  all_goals constructor <;> codec_measure_fixed_step 32 using hc
  all_goals codec_measure_fixed_step 33 using hc
  all_goals simpa [fieldsLoop] using next _

end SszX86.CodecMeasureFixed
