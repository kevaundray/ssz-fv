import SszX86.NatAddCore

namespace SszX86.NatAdd
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def pairMem (m : DataMem) (out pointer payload : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 pointer.toInt
  Mem.storeInt m (out + BitVec.ofNat 64 8) 8 payload.toInt

def successMem (m : DataMem) (out pointer payload : BitVec 64) : DataMem :=
  Mem.storeInt (pairMem m out pointer payload) (out + BitVec.ofNat 64 64) 4 0

def errorMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 32768

def countErrorMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 32768

/-- All success branches share the actual four-byte status store. -/
theorem status_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := Mem.storeInt s.dmem (s.regs.rdi.toBitVec + 64) 4 0}, base + 612)) :
    Eventually (step e) P (s, base + 605) := by
  natadd_output 157 at 64 width 4 using hc mapped hm
  exact next

/-- Normalize-right publication preserves the borrowed pointer and exact count. -/
theorem right_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec s.regs.rcx.toBitVec s.regs.r8.toBitVec},
        base + 612)) :
    Eventually (step e) P (s, base + 585) := by
  natadd_output 150 at 0 width 8 using hc mapped hm
  natadd_output 151 at 8 width 8 using hc mapped hm
  natadd_step 152 using hc
  natadd_output 157 at 64 width 4 using hc mapped hm
  simpa [successMem, pairMem] using next

/-- Normalize-left publication uses the original left pair registers. -/
theorem left_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec s.regs.rdx.toBitVec},
        base + 612)) :
    Eventually (step e) P (s, base + 598) := by
  natadd_output 155 at 0 width 8 using hc mapped hm
  natadd_output 156 at 8 width 8 using hc mapped hm
  natadd_output 157 at 64 width 4 using hc mapped hm
  simpa [successMem, pairMem] using next

theorem small_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec 0 s.regs.rdx.toBitVec}, base + 612)) :
    Eventually (step e) P (s, base + 250) := by
  natadd_output 70 at 0 width 8 using hc mapped hm
  natadd_output 71 at 8 width 8 using hc mapped hm
  natadd_step 72 using hc
  natadd_output 157 at 64 width 4 using hc mapped hm
  simpa [successMem, pairMem] using next

theorem large_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec s.regs.r10.toBitVec s.regs.rcx.toBitVec},
        base + 612)) :
    Eventually (step e) P (s, base + 1387) := by
  natadd_output 370 at 0 width 8 using hc mapped hm
  natadd_output 371 at 8 width 8 using hc mapped hm
  natadd_step 372 using hc
  natadd_output 157 at 64 width 4 using hc mapped hm
  simpa [successMem, pairMem] using next

theorem error_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := errorMem s.dmem s.regs.rdi.toBitVec}, base + 612)) :
    Eventually (step e) P (s, base + 766) := by
  natadd_output 204 at 56 width 8 using hc mapped hm
  natadd_output 205 at 48 width 8 using hc mapped hm
  natadd_output 206 at 40 width 8 using hc mapped hm
  natadd_output 207 at 32 width 8 using hc mapped hm
  natadd_output 208 at 24 width 8 using hc mapped hm
  natadd_output 209 at 16 width 8 using hc mapped hm
  natadd_output 210 at 0 width 8 using hc mapped hm
  natadd_output 211 at 8 width 8 using hc mapped hm
  natadd_output 212 at 64 width 4 using hc mapped hm
  natadd_step 213 using hc
  simpa [errorMem] using next

theorem count_error_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := countErrorMem s.dmem s.regs.rdi.toBitVec}, base + 612)) :
    Eventually (step e) P (s, base + 1399) := by
  natadd_output 373 at 0 width 8 using hc mapped hm
  natadd_output 374 at 8 width 8 using hc mapped hm
  natadd_output 375 at 16 width 8 using hc mapped hm
  natadd_output 376 at 24 width 8 using hc mapped hm
  natadd_output 377 at 32 width 8 using hc mapped hm
  natadd_output 378 at 40 width 8 using hc mapped hm
  natadd_output 379 at 48 width 8 using hc mapped hm
  natadd_output 380 at 56 width 8 using hc mapped hm
  natadd_output 381 at 64 width 4 using hc mapped hm
  natadd_step 382 using hc
  simpa [countErrorMem] using next

end SszX86.NatAdd
