import SszX86.IndicesChunkCountExec

namespace SszX86.IndicesChunkCount
open UintCodec

abbrev OutputMapped (s : MachineData) := Large.Mapped s.dmem s.regs.rdi.toBitVec 72

macro "indices_count_output " row:num " at " offset:num " width " bytes:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 72) (byteCount := $bytes))
  else
    `(tactic| apply Large.mapped_load (capacity := 72) (offset := $offset) («width» := $bytes))
  `(tactic|
    (indices_count_step $row using $hc
     simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply Large.mapped_store
       · decide
     simp only [Effects.All]))

/-- The native error stores touch only active Error fields; the final four
padding bytes of the 72-byte return slot are retained. -/
def errorMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m out 8 1
  let m := Mem.storeInt m (out + 8#64) 8 0
  let m := Mem.storeInt m (out + 16#64) 8 0
  let m := Mem.storeInt m (out + 24#64) 8 0
  let m := Mem.storeInt m (out + 32#64) 8 0
  let m := Mem.storeInt m (out + 40#64) 8 0
  let m := Mem.storeInt m (out + 48#64) 8 0
  let m := Mem.storeInt m (out + 56#64) 8 0
  Mem.storeInt m (out + 64#64) 4 55

def oneMem (m : DataMem) (out : BitVec 64) : DataMem :=
  Mem.storeInt (Mem.storeInt m (out + 8#64) 8 1) out 8 0

def successMem (m : DataMem) (out : BitVec 64) : DataMem :=
  Mem.storeInt m (out + 64#64) 4 0

def countMem (m : DataMem) (out count : BitVec 64) : DataMem :=
  Mem.storeInt (Mem.storeInt m out 8 0) (out + 8#64) 8 count.toInt

theorem noChunkCount_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (mapped : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := errorMem s.dmem s.regs.rdi.toBitVec}, base + 211)) :
    Eventually (step e) P (s, base + 141) := by
  indices_count_output 34 at 0 width 8 using code mapped mapped
  indices_count_output 35 at 8 width 8 using code mapped mapped
  indices_count_output 36 at 16 width 8 using code mapped mapped
  indices_count_output 37 at 24 width 8 using code mapped mapped
  indices_count_output 38 at 32 width 8 using code mapped mapped
  indices_count_output 39 at 40 width 8 using code mapped mapped
  indices_count_output 40 at 48 width 8 using code mapped mapped
  indices_count_output 41 at 56 width 8 using code mapped mapped
  indices_count_output 42 at 64 width 4 using code mapped mapped
  simpa only [errorMem] using next

theorem one_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (mapped : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := oneMem s.dmem s.regs.rdi.toBitVec}, base + 234)) :
    Eventually (step e) P (s, base + 35) := by
  indices_count_output 11 at 8 width 8 using code mapped mapped
  indices_count_output 12 at 0 width 8 using code mapped mapped
  indices_count_step 13 using code
  simpa only [oneMem] using next

theorem success_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (mapped : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec}, base + 241)) :
    Eventually (step e) P (s, base + 234) := by
  indices_count_output 50 at 64 width 4 using code mapped mapped
  simpa only [successMem] using next

def countState (s : MachineData) (count : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec count},
    dmem := countMem s.dmem s.regs.rdi.toBitVec count}

/-- The container length is a physical usize. This does not restrict any
logical Nat stored in descriptor metadata. -/
theorem container_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (count : BitVec 64) (mapped : OutputMapped s)
    (loaded : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 =
      some (count.toNat : Int)) (P : MachineState → Prop)
    (next : Eventually (step e) P (countState s count, base + 234)) :
    Eventually (step e) P (s, base + 219) := by
  indices_count_step 47 using code
  indices_count_load loaded
  indices_count_output 48 at 0 width 8 using code mapped mapped
  indices_count_output 49 at 8 width 8 using code mapped mapped
  simpa only [countState, countMem] using next

end SszX86.IndicesChunkCount
