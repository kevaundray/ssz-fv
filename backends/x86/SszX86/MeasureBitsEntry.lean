import SszX86.MeasureOwned
import SszX86.NatFromU128Core

namespace SszX86.Measure.Bits
open UintCodec

macro "measure_bits_input_load " hl:term : tactic => `(tactic|
  (simp only [MachineData.load, Width.bytes, Width.bits, BitVec.ofInt_add, BitVec.ofInt_toInt]
   rw [($hl)]
   simp only [Effects.All, Delimited.word_cast]))

/-- All three bit descriptors inspect the same byte tag before reading a payload. -/
theorem vector_tag_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rax.toBitVec.setWidth 8 = 3#8
        then base + 90 else base + 3265)) :
    Eventually (step e) P (s, base + 82) := by
  have target := hc.targets ("measure_u3265", 3265) (by decide)
  have selected : s.regs.rax.toBitVec.extractLsb' 0 8 = s.regs.rax.toBitVec.setWidth 8 := by
    rw [← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
  measure_step 19 using hc
  measure_step 20 using hc
  by_cases tag : s.regs.rax.toBitVec.setWidth 8 = 3#8
  · simpa [selected, tag, StatusFlags.from_result, Effects.All] using next _
  · have different : s.regs.rax.toBitVec.setWidth 8 - 3#8 ≠ 0#8 := by bv_omega
    simpa [selected, tag, different, target, StatusFlags.from_result, Effects.All] using next _

theorem list_tag_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rax.toBitVec.setWidth 8 = 3#8
        then base + 887 else base + 3265)) :
    Eventually (step e) P (s, base + 879) := by
  have target := hc.targets ("measure_u3265", 3265) (by decide)
  have selected : s.regs.rax.toBitVec.extractLsb' 0 8 = s.regs.rax.toBitVec.setWidth 8 := by
    rw [← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
  measure_step 100 using hc
  measure_step 101 using hc
  by_cases tag : s.regs.rax.toBitVec.setWidth 8 = 3#8
  · simpa [selected, tag, StatusFlags.from_result, Effects.All] using next _
  · have different : s.regs.rax.toBitVec.setWidth 8 - 3#8 ≠ 0#8 := by bv_omega
    simpa [selected, tag, different, target, StatusFlags.from_result, Effects.All] using next _

theorem progressive_tag_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rax.toBitVec.setWidth 8 = 3#8
        then base + 937 else base + 3265)) :
    Eventually (step e) P (s, base + 929) := by
  have target := hc.targets ("measure_u3265", 3265) (by decide)
  have selected : s.regs.rax.toBitVec.extractLsb' 0 8 = s.regs.rax.toBitVec.setWidth 8 := by
    rw [← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
  measure_step 112 using hc
  measure_step 113 using hc
  by_cases tag : s.regs.rax.toBitVec.setWidth 8 = 3#8
  · simpa [selected, tag, StatusFlags.from_result, Effects.All] using next _
  · have different : s.regs.rax.toBitVec.setWidth 8 - 3#8 ≠ 0#8 := by bv_omega
    simpa [selected, tag, different, target, StatusFlags.from_result, Effects.All] using next _

def vectorLoaded (s : MachineData) (pointer payload low high : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with
      r8 := UInt64.ofBitVec pointer
      rdi := UInt64.ofBitVec payload
      rax := UInt64.ofBitVec low
      rdx := UInt64.ofBitVec high}}

theorem vector_load_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload low high : BitVec 64) (P : MachineState → Prop)
    (hp : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (pointer.toNat : Int))
    (hv : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (payload.toNat : Int))
    (hl : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 32#64) 8 = some (low.toNat : Int))
    (hh : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 40#64) 8 = some (high.toNat : Int))
    (next : Eventually (step e) P (vectorLoaded s pointer payload low high, base + 106)) :
    Eventually (step e) P (s, base + 90) := by
  measure_step 21 using hc
  measure_bits_input_load hp
  measure_step 22 using hc
  measure_bits_input_load hv
  measure_step 23 using hc
  measure_bits_input_load hl
  measure_step 24 using hc
  measure_bits_input_load hh
  simpa [vectorLoaded] using next

def listLoaded (s : MachineData) (pointer payload low high : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with
      r13 := UInt64.ofBitVec pointer
      r12 := UInt64.ofBitVec payload
      r15 := UInt64.ofBitVec low
      r14 := UInt64.ofBitVec high}}

theorem list_load_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload low high : BitVec 64) (P : MachineState → Prop)
    (hp : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (pointer.toNat : Int))
    (hv : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (payload.toNat : Int))
    (hl : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 32#64) 8 = some (low.toNat : Int))
    (hh : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 40#64) 8 = some (high.toNat : Int))
    (next : Eventually (step e) P (listLoaded s pointer payload low high, base + 903)) :
    Eventually (step e) P (s, base + 887) := by
  measure_step 102 using hc
  measure_bits_input_load hp
  measure_step 103 using hc
  measure_bits_input_load hv
  measure_step 104 using hc
  measure_bits_input_load hl
  measure_step 105 using hc
  measure_bits_input_load hh
  simpa [listLoaded] using next

def progressiveLoaded (s : MachineData) (tag pointer payload low high : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec tag
      rbp := UInt64.ofBitVec pointer
      r12 := UInt64.ofBitVec payload
      r15 := UInt64.ofBitVec low
      r14 := UInt64.ofBitVec high}}

/-- Both inactive option words and the full eight-byte option slot are loaded.
Only the low option bit will be inspected; padding has no canonical-value premise. -/
theorem progressive_load_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (tag pointer payload low high : BitVec 64) (P : MachineState → Prop)
    (ht : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (tag.toNat : Int))
    (hp : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (pointer.toNat : Int))
    (hv : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 24#64) 8 = some (payload.toNat : Int))
    (hl : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 32#64) 8 = some (low.toNat : Int))
    (hh : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 40#64) 8 = some (high.toNat : Int))
    (next : Eventually (step e) P (progressiveLoaded s tag pointer payload low high, base + 957)) :
    Eventually (step e) P (s, base + 937) := by
  measure_step 114 using hc
  measure_bits_input_load ht
  measure_step 115 using hc
  measure_bits_input_load hp
  measure_step 116 using hc
  measure_bits_input_load hv
  measure_step 117 using hc
  measure_bits_input_load hl
  measure_step 118 using hc
  measure_bits_input_load hh
  simpa [progressiveLoaded] using next

end SszX86.Measure.Bits
