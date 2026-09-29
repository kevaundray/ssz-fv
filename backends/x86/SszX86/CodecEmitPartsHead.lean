import SszX86.CodecEmitPartsSteps
import SszX86.Udivti3Math

namespace SszX86.CodecEmitParts
open UintCodec

private theorem not_above (a b : BitVec 64) (fits : a.toNat ≤ b.toNat) :
    (!(Udivti3.subFlags a b).cf && !(Udivti3.subFlags a b).zf) = false := by
  by_cases same : a = b
  · simp [same, Udivti3.subFlags_cf, Udivti3.subFlags_zf]
  · have strict : a.toNat < b.toNat := by
      have different : a.toNat ≠ b.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
      omega
    simp [Udivti3.subFlags_cf, Udivti3.subFlags_zf, strict]

def headCompared (s : MachineData) (capacity : BitVec 64) : MachineData :=
  {s with regs := {s.regs with r14 := UInt64.ofBitVec (s.regs.r10.toBitVec + 4)},
    status := Udivti3.subFlags (s.regs.r10.toBitVec + 4) capacity}

/-- The offset head's actual four-byte slice check precedes its store. The
logical head bound also proves the unchecked LEA cannot wrap. -/
theorem head_guard (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (capacity : BitVec 64) (P : MachineState → Prop)
    (length : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 208) 8 = some (capacity.toNat : Int))
    (fits : s.regs.r10.toNat + 4 ≤ capacity.toNat)
    (next : Eventually (step e) P (headCompared s capacity, base + 482)) :
    Eventually (step e) P (s, base + 464) := by
  have bounded : (s.regs.r10.toBitVec + 4).toNat ≤ capacity.toNat := by
    have host := capacity.isLt
    bv_omega
  have branch : Eventually (step e) P (headCompared s capacity, base + 476) := by
    codec_parts_step 114 using code
    simpa only [headCompared, not_above _ _ bounded, Bool.false_eq_true, ↓reduceIte, Effects.All]
      using next
  codec_parts_step 112 using code
  codec_parts_step 113 using code
  codec_parts_load length
  simpa [headCompared, Udivti3.subFlags, BitVec.take, BitVec.signed] using branch

def offsetStored (s : MachineData) (out : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec out},
    dmem := Mem.storeInt s.dmem (out + s.regs.r10.toBitVec) 4
      (s.regs.r8.toBitVec.take 32).toInt}

/-- This is the actual little-endian MOVL offset store. It precedes the variable
body's bounds test and recursive call, exactly as the shared write trace does. -/
theorem offset_store (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (out : BitVec 64) (P : MachineState → Prop)
    (output : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16) 8 = some (out.toNat : Int))
    (mapped : Large.Mapped s.dmem (out + s.regs.r10.toBitVec) 4)
    (next : Eventually (step e) P (offsetStored s out, base + 491)) :
    Eventually (step e) P (s, base + 482) := by
  codec_parts_step 115 using code
  codec_parts_load output
  codec_parts_step 116 using code
  apply Delimited.store_cps
  · simpa only [BitVec.add_zero] using
      Large.mapped_load s.dmem (out + s.regs.r10.toBitVec) 4 0 4 mapped (by decide)
  simpa only [offsetStored, Effects.All] using next

def bodyCompared (s : MachineData) (capacity : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rbp := UInt64.ofBitVec (s.regs.r9.toBitVec + s.regs.r8.toBitVec)},
    status := Udivti3.subFlags (s.regs.r9.toBitVec + s.regs.r8.toBitVec) capacity}

/-- Both native overflow and capacity checks for a variable body follow the
already-committed offset store. Generated-plan bounds discharge both checks. -/
theorem body_guard (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (capacity : BitVec 64) (P : MachineState → Prop)
    (length : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 208) 8 = some (capacity.toNat : Int))
    (fits : s.regs.r9.toNat + s.regs.r8.toNat ≤ capacity.toNat)
    (next : Eventually (step e) P (bodyCompared s capacity, base + 517)) :
    Eventually (step e) P (s, base + 491) := by
  have host := capacity.isLt
  have bounded : (s.regs.r9.toBitVec + s.regs.r8.toBitVec).toNat ≤ capacity.toNat := by bv_omega
  have sumFits : s.regs.r9.toBitVec.toNat + s.regs.r8.toBitVec.toNat ≤ capacity.toNat := by
    simpa only [UInt64.toNat_toBitVec] using fits
  have noCarry : ¬ Udivti3.radix ≤ s.regs.r8.toBitVec.toNat + s.regs.r9.toBitVec.toNat := by
    unfold Udivti3.radix
    omega
  have noCarry' : ¬ Udivti3.radix ≤ s.regs.r9.toBitVec.toNat + s.regs.r8.toBitVec.toNat := by
    unfold Udivti3.radix
    omega
  have branch : Eventually (step e) P (bodyCompared s capacity, base + 511) := by
    codec_parts_step 121 using code
    simpa only [bodyCompared, not_above _ _ bounded, Bool.false_eq_true, ↓reduceIte, Effects.All]
      using next
  codec_parts_step 117 using code
  codec_parts_step 118 using code
  codec_parts_step 119 using code
  simp only [StatusFlags.from_result, Udivti3.cf_add, noCarry, noCarry', decide_false,
    Bool.false_eq_true, ↓reduceIte, Effects.All]
  codec_parts_step 120 using code
  codec_parts_load length
  simpa [bodyCompared, Udivti3.subFlags, BitVec.take, BitVec.signed] using branch

end SszX86.CodecEmitParts
