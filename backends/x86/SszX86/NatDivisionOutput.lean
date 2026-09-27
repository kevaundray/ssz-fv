import SszX86.NatDivisionCore

namespace SszX86.NatDivision
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

abbrev ResultMapped (s : MachineData) : Prop :=
  Large.Mapped s.dmem s.regs.rbx.toBitVec 68

macro "natdiv_result " row:num " at " offset:num " width " byteCount:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 68) (byteCount := $byteCount))
  else
    `(tactic| apply Large.mapped_load (capacity := 68)
      (offset := $offset) («width» := $byteCount))
  `(tactic|
    (natdiv_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply Large.mapped_store
       · decide
     simp only [Effects.All]))

def resultPairMem (m : DataMem) (out pointer payload : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 pointer.toInt
  Mem.storeInt m (out + BitVec.ofNat 64 8) 8 payload.toInt

def resultSuccessMem (m : DataMem) (out pointer payload remainder : BitVec 64) : DataMem :=
  let m := resultPairMem m out pointer payload
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 remainder.toInt
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 0

def resultErrorMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 32768

def resultErrorState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := 8, r14 := 32768, r15 := 0}
    status := flags
    dmem := resultErrorMem s.dmem s.regs.rbx.toBitVec}

/-- Scratch failure clears all seven payload words and writes the private error
niche and its four-byte reason. No arena or borrowed operand byte is written. -/
theorem result_error_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : ResultMapped s) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (resultErrorState s flags, base + 456)) :
    Eventually (step e) P (s, base + 379) := by
  natdiv_result 103 at 56 width 8 using hc mapped hm
  natdiv_result 104 at 48 width 8 using hc mapped hm
  natdiv_result 105 at 40 width 8 using hc mapped hm
  natdiv_result 106 at 32 width 8 using hc mapped hm
  natdiv_result 107 at 24 width 8 using hc mapped hm
  natdiv_result 108 at 16 width 8 using hc mapped hm
  natdiv_result 109 at 0 width 8 using hc mapped hm
  natdiv_step 110 using hc
  natdiv_step 111 using hc
  natdiv_step 112 using hc
  constructor <;> natdiv_result 113 at 8 width 8 using hc mapped hm
  all_goals natdiv_result 114 at 64 width 4 using hc mapped hm
  all_goals simpa [resultErrorState, resultErrorMem] using next _

/-- Shared success tail publishes the remainder and a four-byte zero reason. -/
theorem result_success_tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : ResultMapped s) (hz : s.regs.r14 = 0)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with
        regs := {s.regs with rax := 16}
        dmem := Mem.storeInt
          (Mem.storeInt s.dmem (s.regs.rbx.toBitVec + 16) 8 s.regs.r15.toBitVec.toInt)
          (s.regs.rbx.toBitVec + 64) 4 0}, base + 456)) :
    Eventually (step e) P (s, base + 372) := by
  natdiv_step 101 using hc
  natdiv_step 102 using hc
  natdiv_result 113 at 16 width 8 using hc mapped hm
  natdiv_result 114 at 64 width 4 using hc mapped hm
  simpa [hz] using next

def resultSuccessState (s : MachineData) (flags : StatusFlags) : MachineData :=
  let remainder := s.regs.r15.toBitVec - s.regs.rax.toBitVec * s.regs.r13.toBitVec
  {s with
    regs := {s.regs with rax := 16, r15 := UInt64.ofBitVec remainder}
    status := flags
    dmem := resultSuccessMem s.dmem s.regs.rbx.toBitVec
      s.regs.rdi.toBitVec s.regs.rcx.toBitVec remainder}

/-- The small-quotient path computes the low-word remainder with the real IMUL
and SUB before publishing the quotient pair and common success tail. -/
theorem result_success_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : ResultMapped s) (hz : s.regs.r14 = 0)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (resultSuccessState s flags, base + 456)) :
    Eventually (step e) P (s, base + 358) := by
  have tail : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with rax := UInt64.ofBitVec (s.regs.rax.toBitVec * s.regs.r13.toBitVec)}
        status := flags}, base + 362) := by
    intro flags
    natdiv_step 98 using hc
    natdiv_result 99 at 0 width 8 using hc mapped hm
    natdiv_result 100 at 8 width 8 using hc mapped hm
    apply result_success_tail_cps e base hc
    · repeat' first | exact hm | apply Large.mapped_store
    · exact hz
    · simpa [resultSuccessState, resultSuccessMem, resultPairMem] using next _
  natdiv_step 97 using hc
  repeat' apply And.intro
  all_goals exact tail _

end SszX86.NatDivision
