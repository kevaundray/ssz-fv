import SszX86.NatMulCore
import SszX86.NatMulOwnership
import SszX86.NatMulMemoryOutput

namespace SszX86.NatMul
open UintCodec


def zeroMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 0
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 0

macro "natmul_output " chunk:num ":" index:num " at " offset:num " width " byteCount:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 72) (byteCount := $byteCount))
  else
    `(tactic| apply UintCodec.Large.mapped_load (capacity := 72)
      (offset := $offset) («width» := $byteCount))
  `(tactic|
    (natmul_step $chunk row $index using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply UintCodec.Large.mapped_store
       · decide
     simp only [Effects.All]))

theorem zero_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := zeroMem s.dmem s.regs.rdi.toBitVec}, base + 228)) :
    Eventually (step e) P (s, base + 206) := by
  natmul_output 2:7 at 8 width 8 using hc mapped hm
  natmul_output 2:8 at 0 width 8 using hc mapped hm
  natmul_output 2:9 at 64 width 4 using hc mapped hm
  simpa [zeroMem] using next

theorem result_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Large.Mapped s.dmem s.regs.rax.toBitVec 72)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rax.toBitVec s.regs.rdx.toBitVec s.regs.rcx.toBitVec}, base + 228)) :
    Eventually (step e) P (s, base + 727) := by
  natmul_output 6:13 at 0 width 8 using hc mapped hm
  natmul_output 6:14 at 8 width 8 using hc mapped hm
  natmul_output 6:15 at 64 width 4 using hc mapped hm
  natmul_step 6 row 16 using hc
  simpa [successMem, NatAdd.successMem, NatAdd.pairMem] using next

theorem error_status_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := Mem.storeInt s.dmem (s.regs.rdi.toBitVec + 64) 4 32768}, base + 228)) :
    Eventually (step e) P (s, base + 381) := by
  natmul_output 3:13 at 64 width 4 using hc mapped hm
  natmul_step 3 row 14 using hc
  exact next

theorem error_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := errorMem s.dmem s.regs.rdi.toBitVec}, base + 228)) :
    Eventually (step e) P (s, base + 318) := by
  natmul_output 3:5 at 56 width 8 using hc mapped hm
  natmul_output 3:6 at 48 width 8 using hc mapped hm
  natmul_output 3:7 at 40 width 8 using hc mapped hm
  natmul_output 3:8 at 32 width 8 using hc mapped hm
  natmul_output 3:9 at 24 width 8 using hc mapped hm
  natmul_output 3:10 at 16 width 8 using hc mapped hm
  natmul_output 3:11 at 0 width 8 using hc mapped hm
  natmul_output 3:12 at 8 width 8 using hc mapped hm
  apply error_status_cps e base hc
  · repeat' first | exact hm | apply Large.mapped_store
  simpa [errorMem, NatAdd.errorMem] using next

theorem count_error_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := countErrorMem s.dmem s.regs.rdi.toBitVec}, base + 228)) :
    Eventually (step e) P (s, base + 746) := by
  natmul_output 6:17 at 0 width 8 using hc mapped hm
  natmul_output 6:18 at 8 width 8 using hc mapped hm
  natmul_output 6:19 at 16 width 8 using hc mapped hm
  natmul_output 6:20 at 24 width 8 using hc mapped hm
  natmul_output 6:21 at 32 width 8 using hc mapped hm
  natmul_output 6:22 at 40 width 8 using hc mapped hm
  natmul_output 6:23 at 48 width 8 using hc mapped hm
  natmul_output 6:24 at 56 width 8 using hc mapped hm
  natmul_step 6 row 25 using hc
  apply error_status_cps e base hc
  · repeat' first | exact hm | apply Large.mapped_store
  simpa [countErrorMem, NatAdd.countErrorMem] using next

end SszX86.NatMul
