import SszX86.NatMulWordCore
import SszX86.NatFromU128Memory

namespace SszX86.NatMulWord
open UintCodec

abbrev successMem := NatAdd.successMem
abbrev errorMem := NatAdd.errorMem

/-- The zero fast path writes payload before pointer, as in the linked image. -/
def zeroMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 0
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 0

theorem zero_reads (m : DataMem) (out : BitVec 64) :
    widthLoad (zeroMem m out) out.toNat 8 = some 0 ∧
      widthLoad (zeroMem m out) (out.toNat + 8) 8 = some 0 ∧
      widthLoad (zeroMem m out) (out.toNat + 64) 4 = some 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold zeroMem <;> natadd_result_reads

theorem zero_mem_frame (m : DataMem) (out a : BitVec 64)
    (pair : ∀ i < 16, a ≠ out + BitVec.ofNat 64 i)
    (status : ∀ i < 4, a ≠ out + 64#64 + BitVec.ofNat 64 i) :
    (zeroMem m out).get? a = m.get? a := by
  have statusFrame (m : DataMem) :
      (Mem.storeInt m (out + BitVec.ofNat 64 64) 4 0).get? a = m.get? a := by
    apply memmove_store_lookup_outside
    intro i hi
    exact status i (by simpa only [Int.toBytes_length] using hi)
  have pairFrame (m : DataMem) (off : Nat) (bound : off + 8 ≤ 16) :
      (Mem.storeInt m (out + BitVec.ofNat 64 off) 8 0).get? a = m.get? a := by
    apply memmove_store_lookup_outside
    intro i hi
    have same := pair (off+i) (by simp only [Int.toBytes_length] at hi; omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using same
  simp only [zeroMem, statusFrame, pairFrame _ 0 (by decide), pairFrame _ 8 (by decide)]

theorem zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := zeroMem s.dmem s.regs.rdi.toBitVec}, base + 36)) :
    Eventually (step e) P (s, base + 14) := by
  natmulword_output 0:5 at 8 width 8 using hc mapped hm
  natmulword_output 0:6 at 0 width 8 using hc mapped hm
  natmulword_output 0:7 at 64 width 4 using hc mapped hm
  simpa [zeroMem] using next

/-- Both borrowed publication sites preserve the exact canonical pair. -/
theorem borrowed_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (first : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec s.regs.r9.toBitVec},
        base + 98))
    (second : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec s.regs.r9.toBitVec},
        base + 387)) :
    Eventually (step e) P (s, base + 84) ∧ Eventually (step e) P (s, base + 373) := by
  constructor
  · natmulword_output 0:23 at 0 width 8 using hc mapped hm
    natmulword_output 0:24 at 8 width 8 using hc mapped hm
    natmulword_output 0:25 at 64 width 4 using hc mapped hm
    simpa [successMem, NatAdd.successMem, NatAdd.pairMem] using first
  · natmulword_output 2:31 at 0 width 8 using hc mapped hm
    natmulword_output 3:0 at 8 width 8 using hc mapped hm
    natmulword_output 3:1 at 64 width 4 using hc mapped hm
    simpa [successMem, NatAdd.successMem, NatAdd.pairMem] using second

theorem error_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := errorMem s.dmem s.regs.rdi.toBitVec}, base + 687)) :
    Eventually (step e) P (s, base + 617) := by
  natmulword_output 5:5 at 56 width 8 using hc mapped hm
  natmulword_output 5:6 at 48 width 8 using hc mapped hm
  natmulword_output 5:7 at 40 width 8 using hc mapped hm
  natmulword_output 5:8 at 32 width 8 using hc mapped hm
  natmulword_output 5:9 at 24 width 8 using hc mapped hm
  natmulword_output 5:10 at 16 width 8 using hc mapped hm
  natmulword_output 5:11 at 0 width 8 using hc mapped hm
  natmulword_output 5:12 at 8 width 8 using hc mapped hm
  natmulword_output 5:13 at 64 width 4 using hc mapped hm
  simpa [errorMem, NatAdd.errorMem] using next

/-- Every return is the original RET instruction; no synthetic return edge. -/
theorem ret_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (next : P ({s with regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8)}}, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 36) ∧
    Eventually (step e) P (s, base + 98) ∧
    Eventually (step e) P (s, base + 387) ∧
    Eventually (step e) P (s, base + 701) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · natmulword_step 0:8 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next
  · natmulword_step 0:26 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next
  · natmulword_step 3:2 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next
  · natmulword_step 5:21 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next

end SszX86.NatMulWord
