import SszX86.DelimitedTails

namespace SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Result stores cannot change the original capacity words in the local spills. -/
theorem spill_store_load (m : DataMem) (sp out : BitVec 64)
    (loadOffset storeOffset count : Nat) (value : Int)
    (apart : UintCodec.Large.Disjoint sp out 40 76)
    (hl : loadOffset + 8 ≤ 40) (hs : storeOffset + count ≤ 76) :
    Mem.loadInt (Mem.storeInt m (out + BitVec.ofNat 64 storeOffset) count value)
      (sp + BitVec.ofNat 64 loadOffset) 8 =
      Mem.loadInt m (sp + BitVec.ofNat 64 loadOffset) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  rw [memmove_addr_add, memmove_addr_add]
  exact apart (loadOffset+i) (by omega) (storeOffset+j) (by omega)

def limitHeadMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rdi.toBitVec + BitVec.ofNat 64 64) 8 0
  let m := Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 8) 8 1
  Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 16) 8 0

def limitMem (s : MachineData) (pointer payload : BitVec 64) : DataMem :=
  let m := Mem.storeInt (limitHeadMem s) (s.regs.rdi.toBitVec + BitVec.ofNat 64 24) 8 pointer.toInt
  Mem.storeInt m (s.regs.rdi.toBitVec + BitVec.ofNat 64 32) 8 payload.toInt

def limitReady (s : MachineData) (pointer payload : BitVec 64) : MachineData :=
  {s with
    dmem := limitMem s pointer payload
    regs := {s.regs with rax := 2, rcx := 48, rdx := 40}}

theorem limit_stores_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64)
    (hm : OutputMapped s)
    (apart : UintCodec.Large.Disjoint s.regs.rsp.toBitVec s.regs.rdi.toBitVec 40 76)
    (hpointer : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (pointer.toNat : Int))
    (hpayload : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (payload.toNat : Int))
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (limitReady s pointer payload, base + 807)) :
    Eventually (step e) P (s, base + 454) := by
  have pointerRead : Mem.loadInt (limitHeadMem s) (s.regs.rsp.toBitVec + 8#64) 8 =
      some (pointer.toNat : Int) := by
    simp (disch := first | exact apart | decide) only [limitHeadMem, spill_store_load]
    exact hpointer
  have payloadRead : Mem.loadInt
      (Mem.storeInt (limitHeadMem s) (s.regs.rdi.toBitVec + 24#64) 8 pointer.toInt)
      s.regs.rsp.toBitVec 8 = some (payload.toNat : Int) := by
    have zero : s.regs.rsp.toBitVec = s.regs.rsp.toBitVec + BitVec.ofNat 64 0 := by simp
    rw [zero]
    simp (disch := first | exact apart | decide) only [limitHeadMem, spill_store_load]
    simpa only [BitVec.add_zero] using hpayload
  simp only [limitHeadMem] at pointerRead payloadRead
  delimited_output 107 at 64 width 8 using hc mapped hm
  delimited_output 108 at 56 width 8 using hc mapped hm
  delimited_output 109 at 8 width 8 using hc mapped hm
  delimited_output 110 at 16 width 8 using hc mapped hm
  delimited_step 111 using hc
  delimited_load pointerRead
  delimited_output 112 at 24 width 8 using hc mapped hm
  delimited_step 113 using hc
  delimited_load payloadRead
  delimited_output 114 at 32 width 8 using hc mapped hm
  delimited_step 115 using hc
  delimited_step 116 using hc
  delimited_step 117 using hc
  delimited_step 118 using hc
  simpa [limitReady, limitMem, limitHeadMem] using hp

end SszX86.Delimited
