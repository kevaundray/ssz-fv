import SszX86.BitVectorPadding

namespace SszX86.BitVector
open UintCodec BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The copied private Error, including its unspecified final four padding bytes. -/
structure ErrorImage where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  reason : BitVec 32
  padding : BitVec 32

def divisionErrorMem (m : DataMem) (out : BitVec 64) (image : ErrorImage) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 64) 8 image.w7.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 image.w6.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 image.w5.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 image.w4.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 image.w3.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 image.w1.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 image.w0.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 image.w2.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 72) 4 image.reason.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 76) 4 image.padding.toInt
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1

def divisionErrorState (s : MachineData) (out : BitVec 64) (image : ErrorImage) : MachineData :=
  {s with
    regs := {s.regs with
      rdx := UInt64.ofBitVec out
      rcx := UInt64.ofBitVec (image.padding.setWidth 64)
      rsi := UInt64.ofBitVec image.w0
      rdi := UInt64.ofBitVec image.w1}
    dmem := divisionErrorMem s.dmem out image}

theorem stack_output_read (m : DataMem) (out sp : BitVec 64)
    (loadOff loadCount storeOff storeCount : Nat) (value : Int)
    (outBound : out.toNat + 80 ≤ 2^64) (stackBound : sp.toNat + 224 ≤ 2^64)
    (apart : Body.Apart out.toNat 80 sp.toNat 224)
    (readWithin : loadOff + loadCount ≤ 224) (writeWithin : storeOff + storeCount ≤ 80) :
    Mem.loadInt (Mem.storeInt m (out + BitVec.ofNat 64 storeOff) storeCount value)
      (sp + BitVec.ofNat 64 loadOff) loadCount =
      Mem.loadInt m (sp + BitVec.ofNat 64 loadOff) loadCount := by
  apply load_store_disjoint
  intro i hi j hj
  unfold Body.Apart at apart
  bv_omega

macro "bitvector_error_load " row:num " using " hc:term " word " hl:term : tactic => `(tactic|
  (bitvector_step $row using $hc
   simp (disch := first | assumption | omega | decide)
     [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, stack_output_read, ($hl), Delimited.word_cast]))

/-- Actual first-helper failure copy. It forwards the native Error verbatim and
writes the four padding bytes the native body copies, without changing scratch. -/
theorem division_error_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (out : BitVec 64) (image : ErrorImage)
    (hm : Large.Mapped s.dmem out 80)
    (outBound : out.toNat + 80 ≤ 2^64) (stackBound : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64)
    (apart : Body.Apart out.toNat 80 s.regs.rsp.toBitVec.toNat 224)
    (houtput : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (out.toNat : Int))
    (h0 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 120#64) 8 = some (image.w0.toNat : Int))
    (h1 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 128#64) 8 = some (image.w1.toNat : Int))
    (h2 : s.regs.r13.toBitVec = image.w2)
    (h3 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 40#64) 8 = some (image.w3.toNat : Int))
    (h4 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 48#64) 8 = some (image.w4.toNat : Int))
    (h5 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 56#64) 8 = some (image.w5.toNat : Int))
    (h6 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 64#64) 8 = some (image.w6.toNat : Int))
    (h7 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 72#64) 8 = some (image.w7.toNat : Int))
    (hreason : s.regs.rax.toBitVec.setWidth 32 = image.reason)
    (hpadding : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 84#64) 4 = some (image.padding.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (divisionErrorState s out image, base + 7720)) :
    Eventually (step e) P (s, base + 197) := by
  have signedReason : (s.regs.rax.toNat : Int).bmod 4294967296 = image.reason.toInt := by
    simpa only [BitVec.toInt_setWidth, UInt64.toNat_toBitVec,
      show (2^32 : Nat) = 4294967296 by decide] using congrArg BitVec.toInt hreason
  bitvector_error_load 18 using hc word h7
  bitvector_error_load 19 using hc word houtput
  bitvector_output 20 at 64 width 8 using hc mapped hm
  bitvector_error_load 21 using hc word h6
  bitvector_output 22 at 56 width 8 using hc mapped hm
  bitvector_error_load 23 using hc word h5
  bitvector_output 24 at 48 width 8 using hc mapped hm
  bitvector_error_load 25 using hc word h3
  bitvector_error_load 26 using hc word h4
  bitvector_output 27 at 40 width 8 using hc mapped hm
  bitvector_output 28 at 32 width 8 using hc mapped hm
  bitvector_error_load 29 using hc word hpadding
  bitvector_error_load 30 using hc word h0
  bitvector_error_load 31 using hc word h1
  bitvector_output 32 at 16 width 8 using hc mapped hm
  bitvector_output 33 at 8 width 8 using hc mapped hm
  bitvector_output 34 at 24 width 8 using hc mapped hm
  bitvector_output 35 at 72 width 4 using hc mapped hm
  bitvector_output 36 at 76 width 4 using hc mapped hm
  bitvector_output 37 at 0 width 8 using hc mapped hm
  bitvector_step 38 using hc
  with_reducible
    simpa [divisionErrorState, divisionErrorMem, h2, signedReason] using next

theorem division_error_frame (m : DataMem) (out a : BitVec 64) (image : ErrorImage)
    (outside : ∀ i < 80, a ≠ out + BitVec.ofNat 64 i) :
    (divisionErrorMem m out image).get? a = m.get? a := by
  simp (disch := first | assumption | omega | decide) only
    [divisionErrorMem, store_frame (limit := 80)]

end SszX86.BitVector
