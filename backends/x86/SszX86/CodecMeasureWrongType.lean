import SszX86.CodecMeasureDecode
import SszX86.CodecMeasurePrimitiveBinding
import SszX86.MeasureOutput

namespace SszX86.CodecMeasure
open BoolCodec UintCodec

/-- Every sequence-like compound checks its root tag before reading children. -/
theorem vector_wrong_type (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (wrong : s.regs.rax.toBitVec.setWidth 8 ≠ 4)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 3265)) :
    Eventually (step e) P (s, base + 702) := by
  have target := code.targets ("measure_u3265", 3265) (by decide)
  codec_measure_step 2 row 36 using code
  codec_measure_step 2 row 37 using code
  simpa [StatusFlags.from_result, wrong, target, Effects.All] using next _

theorem list_wrong_type (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (wrong : s.regs.rax.toBitVec.setWidth 8 ≠ 4)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 3265)) :
    Eventually (step e) P (s, base + 1026) := by
  have target := code.targets ("measure_u3265", 3265) (by decide)
  codec_measure_step 3 row 50 using code
  codec_measure_step 3 row 51 using code
  simpa [StatusFlags.from_result, wrong, target, Effects.All] using next _

theorem progressive_list_wrong_type (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (wrong : s.regs.rax.toBitVec.setWidth 8 ≠ 4)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 3265)) :
    Eventually (step e) P (s, base + 394) := by
  have target := code.targets ("measure_u3265", 3265) (by decide)
  codec_measure_step 1 row 31 using code
  codec_measure_step 1 row 32 using code
  simpa [StatusFlags.from_result, wrong, target, Effects.All] using next _

theorem container_wrong_type (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (wrong : s.regs.rax.toBitVec.setWidth 8 ≠ 4)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rdx := 8}, status := flags}, base + 3265)) :
    Eventually (step e) P (s, base + 977) := by
  have target := code.targets ("measure_u3265", 3265) (by decide)
  codec_measure_step 3 row 39 using code
  codec_measure_step 3 row 40 using code
  codec_measure_step 3 row 41 using code
  simpa [StatusFlags.from_result, wrong, target, Effects.All] using next _

theorem progressive_container_wrong_type (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (wrong : s.regs.rax.toBitVec.setWidth 8 ≠ 4)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rdx := 24}, status := flags}, base + 3265)) :
    Eventually (step e) P (s, base + 64) := by
  codec_measure_step 0 row 19 using code
  codec_measure_step 0 row 20 using code
  codec_measure_step 0 row 21 using code
  simp only [StatusFlags.from_result, wrong, Bool.false_eq_true, ↓reduceIte]
  codec_measure_step 0 row 22 using code
  simpa [Effects.All, Int64.add_assoc] using next _

/-- A union with any non-union value refuses before selector lookup or allocation. -/
theorem union_wrong_type (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (wrong : s.regs.rax.toBitVec.setWidth 8 ≠ 5)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 3265)) :
    Eventually (step e) P (s, base + 168) := by
  have target := code.targets ("measure_u3265", 3265) (by decide)
  codec_measure_step 0 row 42 using code
  codec_measure_step 0 row 43 using code
  simpa [StatusFlags.from_result, wrong, target, Effects.All] using next _

/-- The compound error join reuses the identical actual 68-byte publication
proved for primitive wrong-type paths; no padding byte is prescribed. -/
theorem wrong_type_publish (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (mapped : Measure.OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := Measure.wrongTypeMem s.dmem s.regs.rbx.toBitVec}, base + 3335)) :
    Eventually (step e) P (s, base + 3265) :=
  Measure.wrong_type_cps e base code.primitive s mapped P next

end SszX86.CodecMeasure
