import SszX86.MeasureOutputCore

namespace SszX86.Measure
open UintCodec

/-- Publish the original represented size, without touching unused Plan padding. -/
theorem success_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := planMem s.dmem s.regs.rbx.toBitVec s.regs.rcx.toBitVec s.regs.rax.toBitVec},
        base + 3335)) :
    Eventually (step e) P (s, base + 3052) := by
  measure_output 436 at 0 measureByteCount 8 using hc measureMapping hm
  measure_output 437 at 8 measureByteCount 8 using hc measureMapping hm
  measure_output 438 at 16 measureByteCount 8 using hc measureMapping hm
  measure_output 439 at 24 measureByteCount 8 using hc measureMapping hm
  measure_output 440 at 32 measureByteCount 8 using hc measureMapping hm
  measure_output 441 at 64 measureByteCount 4 using hc measureMapping hm
  measure_step 442 using hc
  simpa [planMem] using next

/-- The scalar-size join explicitly constructs Small by clearing ECX. -/
theorem small_success_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with rcx := 0}
        status := flags
        dmem := planMem s.dmem s.regs.rbx.toBitVec 0 s.regs.rax.toBitVec}, base + 3335)) :
    Eventually (step e) P (s, base + 3050) := by
  measure_step 435 using hc
  constructor <;> apply success_cps e base hc
  all_goals first | exact hm | exact next _

/-- Every wrong-type branch reaches this same complete NativeError publication. -/
theorem wrong_type_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := wrongTypeMem s.dmem s.regs.rbx.toBitVec}, base + 3335)) :
    Eventually (step e) P (s, base + 3265) := by
  measure_output 459 at 0 measureByteCount 8 using hc measureMapping hm
  measure_output 460 at 8 measureByteCount 8 using hc measureMapping hm
  measure_output 461 at 16 measureByteCount 8 using hc measureMapping hm
  measure_output 462 at 24 measureByteCount 8 using hc measureMapping hm
  measure_output 463 at 32 measureByteCount 8 using hc measureMapping hm
  measure_output 464 at 40 measureByteCount 8 using hc measureMapping hm
  measure_output 465 at 48 measureByteCount 8 using hc measureMapping hm
  measure_output 466 at 56 measureByteCount 8 using hc measureMapping hm
  measure_output 467 at 64 measureByteCount 4 using hc measureMapping hm
  simpa [wrongTypeMem] using next

/-- Inlined count-constructor failure has the accepted exact arithmetic payload. -/
theorem scratch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := NatAdd.errorMem s.dmem s.regs.rbx.toBitVec}, base + 3335)) :
    Eventually (step e) P (s, base + 2963) := by
  measure_output 420 at 56 measureByteCount 8 using hc measureMapping hm
  measure_output 421 at 48 measureByteCount 8 using hc measureMapping hm
  measure_output 422 at 40 measureByteCount 8 using hc measureMapping hm
  measure_output 423 at 32 measureByteCount 8 using hc measureMapping hm
  measure_output 424 at 24 measureByteCount 8 using hc measureMapping hm
  measure_output 425 at 16 measureByteCount 8 using hc measureMapping hm
  measure_output 426 at 0 measureByteCount 8 using hc measureMapping hm
  measure_output 427 at 8 measureByteCount 8 using hc measureMapping hm
  measure_output 428 at 64 measureByteCount 4 using hc measureMapping hm
  measure_step 429 using hc
  simpa [NatAdd.errorMem] using next

/-- Scope publication preserves the descriptor's exact padded Nat representation. -/
theorem bytes_scope_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := scalarErrorMem s.dmem s.regs.rbx.toBitVec 3 s.regs.rcx.toBitVec s.regs.rdx.toBitVec s.regs.rax.toBitVec},
        base + 3335)) :
    Eventually (step e) P (s, base + 3095) := by
  measure_output 443 at 56 measureByteCount 8 using hc measureMapping hm
  measure_output 444 at 48 measureByteCount 8 using hc measureMapping hm
  measure_output 445 at 0 measureByteCount 8 using hc measureMapping hm
  measure_output 446 at 8 measureByteCount 8 using hc measureMapping hm
  measure_output 447 at 16 measureByteCount 8 using hc measureMapping hm
  measure_output 448 at 24 measureByteCount 8 using hc measureMapping hm
  measure_step 449 using hc
  measure_output 450 at 32 measureByteCount 8 using hc measureMapping hm
  measure_output 451 at 40 measureByteCount 8 using hc measureMapping hm
  measure_output 452 at 64 measureByteCount 4 using hc measureMapping hm
  measure_step 453 using hc
  simpa [scalarErrorMem] using next

/-- Limit publication uses exactly the same represented arguments as Scope. -/
theorem bytes_limit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := scalarErrorMem s.dmem s.regs.rbx.toBitVec 2 s.regs.rcx.toBitVec s.regs.rdx.toBitVec s.regs.rax.toBitVec},
        base + 3335)) :
    Eventually (step e) P (s, base + 2252) := by
  measure_output 329 at 56 measureByteCount 8 using hc measureMapping hm
  measure_output 330 at 48 measureByteCount 8 using hc measureMapping hm
  measure_output 331 at 0 measureByteCount 8 using hc measureMapping hm
  measure_output 332 at 8 measureByteCount 8 using hc measureMapping hm
  measure_output 333 at 16 measureByteCount 8 using hc measureMapping hm
  measure_output 334 at 24 measureByteCount 8 using hc measureMapping hm
  measure_step 335 using hc
  measure_output 336 at 32 measureByteCount 8 using hc measureMapping hm
  measure_output 337 at 40 measureByteCount 8 using hc measureMapping hm
  measure_output 338 at 64 measureByteCount 4 using hc measureMapping hm
  measure_step 339 using hc
  simpa [scalarErrorMem] using next

end SszX86.Measure
