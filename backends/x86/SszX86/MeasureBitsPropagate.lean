import SszX86.MeasureOutputCore
import SszX86.NatFromU128Core

namespace SszX86.Measure.Bits
open UintCodec BoolCodec

/-- Output stores cannot disturb the yet-to-be-copied local error words. -/
theorem stack_output_read (m : DataMem) (sp out : BitVec 64)
    (a n b k : Nat) (value : Int)
    (apart : Large.Disjoint sp out 216 72)
    (ha : a + n ≤ 216) (hb : b + k ≤ 72) :
    Mem.loadInt (Mem.storeInt m (out + BitVec.ofNat 64 b) k value)
      (sp + BitVec.ofNat 64 a) n = Mem.loadInt m (sp + BitVec.ofNat 64 a) n := by
  apply load_store_disjoint
  intro i hi j hj
  simpa only [memmove_addr_add] using apart (a+i) (by omega) (b+j) (by omega)

/-- Six remaining payload words and the actual, unconstrained copied padding. -/
structure ErrorTail where
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  padding : BitVec 32

def propagatedMem (s : MachineData) (v : ErrorTail) : DataMem :=
  let out := s.regs.rbx.toBitVec
  let m := Mem.storeInt s.dmem (out + BitVec.ofNat 64 56) 8 v.w7.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 v.w6.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 v.w5.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 v.w4.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 v.w3.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 v.w2.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 s.regs.rcx.toBitVec.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 s.regs.rax.toBitVec.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 64) 4 (s.regs.rdx.toBitVec.setWidth 32).toInt
  Mem.storeInt m (out + BitVec.ofNat 64 68) 4 v.padding.toInt

def propagated (s : MachineData) (v : ErrorTail) : MachineData :=
  {s with
    dmem := propagatedMem s v
    regs := {s.regs with
      rsi := UInt64.ofBitVec (v.padding.setWidth 64)
      rdi := UInt64.ofBitVec v.w3}}

macro "measure_bits_error_load " row:num " using " hc:term " measureErrorWord " hl:term : tactic => `(tactic|
  (measure_step $row using $hc
   simp (disch := first | assumption | omega | decide)
     [MachineData.load, Width.bytes, Width.bits, Effects.All,
       BitVec.ofInt_add, BitVec.ofInt_toInt, stack_output_read, ($hl), Delimited.word_cast]))

/-- Actual2141..2212 propagation, including the otherwise unspecified dword at
result+68. There is no memcpy oracle or narrowed68-byte replacement. -/
theorem propagate_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v : ErrorTail) (P : MachineState → Prop)
    (hm : OutputMapped s)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 216 72)
    (h2 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 40#64) 8 = some (v.w2.toNat : Int))
    (h3 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 48#64) 8 = some (v.w3.toNat : Int))
    (h4 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 56#64) 8 = some (v.w4.toNat : Int))
    (h5 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 64#64) 8 = some (v.w5.toNat : Int))
    (h6 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 72#64) 8 = some (v.w6.toNat : Int))
    (h7 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 80#64) 8 = some (v.w7.toNat : Int))
    (hpad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 92#64) 4 = some (v.padding.toNat : Int))
    (next : Eventually (step e) P (propagated s v, base + 3335)) :
    Eventually (step e) P (s, base + 2141) := by
  measure_bits_error_load 302 using hc measureErrorWord h7
  measure_output 303 at 56 measureByteCount 8 using hc measureMapping hm
  measure_bits_error_load 304 using hc measureErrorWord h6
  measure_output 305 at 48 measureByteCount 8 using hc measureMapping hm
  measure_bits_error_load 306 using hc measureErrorWord h5
  measure_output 307 at 40 measureByteCount 8 using hc measureMapping hm
  measure_bits_error_load 308 using hc measureErrorWord h4
  measure_output 309 at 32 measureByteCount 8 using hc measureMapping hm
  measure_bits_error_load 310 using hc measureErrorWord h2
  measure_bits_error_load 311 using hc measureErrorWord h3
  measure_output 312 at 24 measureByteCount 8 using hc measureMapping hm
  measure_output 313 at 16 measureByteCount 8 using hc measureMapping hm
  measure_bits_error_load 314 using hc measureErrorWord hpad
  measure_output 315 at 0 measureByteCount 8 using hc measureMapping hm
  measure_output 316 at 8 measureByteCount 8 using hc measureMapping hm
  measure_output 317 at 64 measureByteCount 4 using hc measureMapping hm
  measure_output 318 at 68 measureByteCount 4 using hc measureMapping hm
  measure_step 319 using hc
  simpa [propagated, propagatedMem, BitVec.add_assoc] using next

end SszX86.Measure.Bits
