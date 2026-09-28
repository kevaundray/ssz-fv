import SszX86.MeasureOutputCore
import SszX86.NatFromU128Core

namespace SszX86.Measure.Bits
open UintCodec

/-- The original represented bound and the newly constructed count are both
retained, including a Large count's allocation pointer. -/
def limitMem (m : DataMem) (out expectedPointer expectedPayload actualPointer actualPayload : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 expectedPointer.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 expectedPayload.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 actualPointer.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 actualPayload.toInt
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 2

theorem list_limit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (hm : OutputMapped s)
    (next : Eventually (step e) P
      ({s with dmem := limitMem s.dmem s.regs.rbx.toBitVec s.regs.r13.toBitVec s.regs.r12.toBitVec s.regs.rbp.toBitVec s.regs.r15.toBitVec}, base + 3335)) :
    Eventually (step e) P (s, base + 1366) := by
  measure_output 155 at 56 measureByteCount 8 using hc measureMapping hm
  measure_output 156 at 48 measureByteCount 8 using hc measureMapping hm
  measure_output 157 at 0 measureByteCount 8 using hc measureMapping hm
  measure_output 158 at 8 measureByteCount 8 using hc measureMapping hm
  measure_output 159 at 16 measureByteCount 8 using hc measureMapping hm
  measure_output 160 at 24 measureByteCount 8 using hc measureMapping hm
  measure_output 161 at 32 measureByteCount 8 using hc measureMapping hm
  measure_output 162 at 40 measureByteCount 8 using hc measureMapping hm
  measure_output 163 at 64 measureByteCount 4 using hc measureMapping hm
  measure_step 164 using hc
  simpa [limitMem] using next

theorem progressive_limit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (hm : OutputMapped s)
    (next : Eventually (step e) P
      ({s with dmem := limitMem s.dmem s.regs.rbx.toBitVec s.regs.rbp.toBitVec s.regs.r12.toBitVec s.regs.r13.toBitVec s.regs.rdi.toBitVec}, base + 3335)) :
    Eventually (step e) P (s, base + 1562) := by
  measure_output 199 at 56 measureByteCount 8 using hc measureMapping hm
  measure_output 200 at 48 measureByteCount 8 using hc measureMapping hm
  measure_output 201 at 0 measureByteCount 8 using hc measureMapping hm
  measure_output 202 at 8 measureByteCount 8 using hc measureMapping hm
  measure_output 203 at 16 measureByteCount 8 using hc measureMapping hm
  measure_output 204 at 24 measureByteCount 8 using hc measureMapping hm
  measure_output 205 at 32 measureByteCount 8 using hc measureMapping hm
  measure_output 206 at 40 measureByteCount 8 using hc measureMapping hm
  measure_output 207 at 64 measureByteCount 4 using hc measureMapping hm
  measure_step 208 using hc
  simpa [limitMem] using next

def scopeTailMem (m : DataMem) (out actualPointer actualPayload : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 actualPointer.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 actualPayload.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 3

theorem scope_tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (hm : OutputMapped s)
    (next : Eventually (step e) P
      ({s with dmem := scopeTailMem s.dmem s.regs.rbx.toBitVec s.regs.rcx.toBitVec s.regs.rax.toBitVec}, base + 3335)) :
    Eventually (step e) P (s, base + 2912) := by
  measure_output 412 at 0 measureByteCount 8 using hc measureMapping hm
  measure_output 413 at 8 measureByteCount 8 using hc measureMapping hm
  measure_output 414 at 32 measureByteCount 8 using hc measureMapping hm
  measure_output 415 at 40 measureByteCount 8 using hc measureMapping hm
  measure_output 416 at 48 measureByteCount 8 using hc measureMapping hm
  measure_output 417 at 56 measureByteCount 8 using hc measureMapping hm
  measure_output 418 at 64 measureByteCount 4 using hc measureMapping hm
  measure_step 419 using hc
  simpa [scopeTailMem] using next

def scopePrepared (s : MachineData) (pointer payload : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rdx := UInt64.ofBitVec pointer, rsi := UInt64.ofBitVec payload}
    status := flags
    dmem := Mem.storeInt
      (Mem.storeInt s.dmem (s.regs.rbx.toBitVec + 24#64) 8 payload.toInt)
      (s.regs.rbx.toBitVec + 16#64) 8 pointer.toInt}

/-- Reload the original, potentially padded descriptor Nat only after count
construction; neither semantic rejection nor its payload rolls back allocation. -/
theorem scope_prepare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64) (P : MachineState → Prop)
    (hm : OutputMapped s)
    (hp : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (pointer.toNat : Int))
    (hv : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (payload.toNat : Int))
    (next : ∀ flags, Eventually (step e) P (scopePrepared s pointer payload flags, base + 2912)) :
    Eventually (step e) P (s, base + 2893) := by
  have wrapped (value : Int) :
      BitVec.ofInt 64 (value.bmod 18446744073709551616) = BitVec.ofInt 64 value := by
    simpa only [BitVec.toInt_ofInt, Nat.reducePow] using
      (BitVec.ofInt_toInt (x := BitVec.ofInt 64 value))
  have advanced : BitVec.ofInt 64 ((8 + s.regs.rsi.toBitVec.toInt).bmod 18446744073709551616) =
      s.regs.rsi.toBitVec + 8#64 := by
    rw [wrapped, BitVec.ofInt_add, BitVec.ofInt_toInt]
    exact BitVec.add_comm _ _
  measure_step 407 using hc
  measure_step 408 using hc
  simp only [MachineData.load, Width.bytes, Width.bits, advanced]
  rw [hp]
  simp only [Effects.All, Delimited.word_cast]
  measure_step 409 using hc
  simp only [MachineData.load, Width.bytes, Width.bits,
    advanced, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hv]
  simp only [Effects.All, Delimited.word_cast]
  measure_output 410 at 24 measureByteCount 8 using hc measureMapping hm
  measure_output 411 at 16 measureByteCount 8 using hc measureMapping hm
  simpa [scopePrepared] using next _

end SszX86.Measure.Bits
