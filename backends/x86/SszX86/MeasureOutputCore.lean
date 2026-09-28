import SszX86.MeasureCore

namespace SszX86.Measure
open UintCodec

abbrev OutputMapped (s : MachineData) := Large.Mapped s.dmem s.regs.rbx.toBitVec 72

macro "measure_output " row:num " at " off:num " measureByteCount " byteCount:num
    " using " hc:term " measureMapping " hm:term : tactic => do
  let loadTac ← if off.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 72) (byteCount := $byteCount))
  else
    `(tactic| apply UintCodec.Large.mapped_load (capacity := 72)
      («offset» := $off) («width» := $byteCount))
  `(tactic|
    (measure_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply UintCodec.Large.mapped_store
       · decide
     simp only [Effects.All]))

/-- Actual store order of the common successful Plan publication. -/
def planMem (m : DataMem) (out pointer payload : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 8
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 pointer.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 payload.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 0
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 0

def wrongTypeMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 1

/-- Byte Scope and Limit stores have the same order, differing only in status. -/
def scalarErrorMem (m : DataMem) (out : BitVec 64) (code : Nat)
    (expectedPointer expectedPayload actualPayload : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 expectedPointer.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 expectedPayload.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 actualPayload.toInt
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 (code : Int)

end SszX86.Measure
