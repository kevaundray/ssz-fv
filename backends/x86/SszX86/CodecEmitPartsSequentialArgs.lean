import SszX86.CodecEmitPartsSteps

namespace SszX86.CodecEmitParts

def sequentialCallState (s : MachineData) (out capacity result desc : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec out
    rcx := 0
    rdx := s.regs.r12
    rsi := UInt64.ofBitVec desc
    rdi := UInt64.ofBitVec result
    r8 := UInt64.ofBitVec (out + s.regs.rbx.toBitVec)
    r9 := UInt64.ofBitVec (capacity - s.regs.rbx.toBitVec)}, status := flags}

/-- Fixed repeated children receive the remaining output suffix and a literal
null plan pointer. The real subtraction guard is discharged from the cursor
bound before the next actual recursive CALL can execute. -/
theorem sequential_repeated_args (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (out capacity : BitVec 64) (P : MachineState → Prop)
    (output : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16) 8 = some (out.toNat : Int))
    (length : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 208) 8 = some (capacity.toNat : Int))
    (fits : s.regs.rbx.toNat ≤ capacity.toNat)
    (next : ∀ flags, Eventually (step e) P
      (sequentialCallState s out capacity s.regs.r15.toBitVec s.regs.r14.toBitVec flags,
        base + 773)) :
    Eventually (step e) P (s, base + 736) := by
  have noBorrow : ¬ capacity.toNat < s.regs.rbx.toBitVec.toNat := by
    simpa only [UInt64.toNat_toBitVec] using (by omega : ¬ capacity.toNat < s.regs.rbx.toNat)
  codec_parts_step 176 using code
  codec_parts_load length
  codec_parts_step 177 using code
  codec_parts_step 178 using code
  simp only [StatusFlags.from_result, NatCompare.cf_sub, noBorrow, decide_false,
    Bool.false_eq_true, ↓reduceIte, Effects.All]
  codec_parts_step 179 using code
  codec_parts_load output
  codec_parts_step 180 using code
  codec_parts_step 181 using code
  codec_parts_step 182 using code
  codec_parts_step 183 using code
  codec_parts_step 184 using code
  constructor <;> simpa [sequentialCallState, Effects.All] using next _

/-- Fixed fields use the same suffix loop, but read the next field descriptor
through its actual 24-byte field slot. No retained child Plan is supplied. -/
theorem sequential_field_args (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (out capacity desc : BitVec 64) (P : MachineState → Prop)
    (output : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16) 8 = some (out.toNat : Int))
    (length : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 208) 8 = some (capacity.toNat : Int))
    (descriptor : Mem.loadInt s.dmem s.regs.rbp.toBitVec 8 = some (desc.toNat : Int))
    (fits : s.regs.rbx.toNat ≤ capacity.toNat)
    (next : ∀ flags, Eventually (step e) P
      (sequentialCallState s out capacity (s.regs.rsp.toBitVec + 24) desc flags, base + 660)) :
    Eventually (step e) P (s, base + 620) := by
  have noBorrow : ¬ capacity.toNat < s.regs.rbx.toBitVec.toNat := by
    simpa only [UInt64.toNat_toBitVec] using (by omega : ¬ capacity.toNat < s.regs.rbx.toNat)
  codec_parts_step 147 using code
  codec_parts_load length
  codec_parts_step 148 using code
  codec_parts_step 149 using code
  simp only [StatusFlags.from_result, NatCompare.cf_sub, noBorrow, decide_false,
    Bool.false_eq_true, ↓reduceIte, Effects.All]
  codec_parts_step 150 using code
  codec_parts_load descriptor
  codec_parts_step 151 using code
  codec_parts_load output
  codec_parts_step 152 using code
  codec_parts_step 153 using code
  codec_parts_step 154 using code
  codec_parts_step 155 using code
  constructor <;> simpa [sequentialCallState, Effects.All] using next _

end SszX86.CodecEmitParts
