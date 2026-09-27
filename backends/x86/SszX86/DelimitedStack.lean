import SszX86.DelimitedReturn

namespace SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Every stack access is inside the caller's 104-byte activation reservation. -/
theorem activation_load (m : DataMem) (sp : BitVec 64) (offset : Nat)
    (hm : UintCodec.Large.Mapped m (sp - 104) 104)
    (lo : 8 ≤ offset) (hi : offset ≤ 104) :
    ∃ old, Mem.loadInt m (sp - BitVec.ofNat 64 offset) 8 = some old := by
  have ha : sp - BitVec.ofNat 64 offset =
      (sp - 104) + BitVec.ofNat 64 (104-offset) := by bv_omega
  rw [ha]
  exact UintCodec.Large.mapped_load m (sp - 104) 104 (104-offset) 8 hm (by omega)

def pushedMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 s.regs.rbp.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 16) 8 s.regs.r15.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 24) 8 s.regs.r14.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 32) 8 s.regs.r13.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 40) 8 s.regs.r12.toBitVec.toInt
  Mem.storeInt m (s.regs.rsp.toBitVec - 48) 8 s.regs.rbx.toBitVec.toInt

def pushedState (s : MachineData) : MachineData :=
  {s with
    dmem := pushedMem s
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 48)}}

macro "delimited_push " row:num " offset " offset:num " using " hc:term
    " mapped " hm:term : tactic => `(tactic|
  (delimited_step $row using $hc
   try simp only [BitVec.sub_sub]
   apply store_cps
   · have hm' := $hm
     apply activation_load (offset := $offset)
     · repeat' first | exact hm' | apply UintCodec.Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

/-- Six actual pushes, in the linked SysV register order. -/
theorem pushes_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : UintCodec.Large.Mapped s.dmem (s.regs.rsp.toBitVec - 104) 104)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (pushedState s, base + 32)) :
    Eventually (step e) P (s, base + 22) := by
  delimited_push 5 offset 8 using hc mapped hm
  delimited_push 6 offset 16 using hc mapped hm
  delimited_push 7 offset 24 using hc mapped hm
  delimited_push 8 offset 32 using hc mapped hm
  delimited_push 9 offset 40 using hc mapped hm
  delimited_push 10 offset 48 using hc mapped hm
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 - 8 = s.regs.rsp - 48 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  simpa [pushedState, pushedMem, Width.bytesv, BitVec.sub_sub, stackReg] using hp

def localState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 40#64)
      r13 := UInt64.ofBitVec (s.regs.rcx.toBitVec - 1#64)
      rax := UInt64.ofBitVec ((s.regs.rax.toBitVec.setWidth 8).setWidth 64)}
    status := flags}

/-- Forty local bytes are reserved before lowering BSR, without a memory write. -/
theorem locals_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (localState s flags, base + 43)) :
    Eventually (step e) P (s, base + 32) := by
  have preceding : BitVec.ofInt 64 (s.regs.rcx.toBitVec.toInt + (-1)) =
      s.regs.rcx.toBitVec - 1#64 := by
    have minus : BitVec.ofInt 64 (-1) = -(1#64) := by decide
    simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, minus, ← BitVec.sub_eq_add_neg]
  delimited_step 11 using hc
  delimited_step 12 using hc
  delimited_step 13 using hc
  simpa only [localState, preceding, UInt64.ofBitVec_sub, UInt64.ofBitVec_toBitVec,
    UInt64.ofBitVec_ofNat] using hp _

/-- Saved words are observed at the main-frame pointer, before the epilogue. -/
structure SavedAt (m : DataMem) (sp : BitVec 64) (original : MachineData) : Prop where
  rbx : Mem.loadInt m (sp + 40#64) 8 = some (original.regs.rbx.toBitVec.toInt.take 64)
  r12 : Mem.loadInt m (sp + 48#64) 8 = some (original.regs.r12.toBitVec.toInt.take 64)
  r13 : Mem.loadInt m (sp + 56#64) 8 = some (original.regs.r13.toBitVec.toInt.take 64)
  r14 : Mem.loadInt m (sp + 64#64) 8 = some (original.regs.r14.toBitVec.toInt.take 64)
  r15 : Mem.loadInt m (sp + 72#64) 8 = some (original.regs.r15.toBitVec.toInt.take 64)
  rbp : Mem.loadInt m (sp + 80#64) 8 = some (original.regs.rbp.toBitVec.toInt.take 64)

def restoredState (s original : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 88)
      rbx := original.regs.rbx
      rbp := original.regs.rbp
      r12 := original.regs.r12
      r13 := original.regs.r13
      r14 := original.regs.r14
      r15 := original.regs.r15}
    status := flags}

theorem take_cast (value : BitVec 64) : BitVec.ofInt 64 (value.toInt.take 64) = value := by
  simpa only [ofBytes_toBytes] using BitVec.ofInt_ofBytes_toBytes 64 8 rfl value

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "delimited_stack_load " hw:term : tactic => `(tactic|
  simp [MachineData.load, Effects.All, ($hw), take_cast,
    BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
    UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc])

/-- The complete real pop sequence restores every SysV saved register. -/
theorem restore_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s original : MachineData) (saved : SavedAt s.dmem s.regs.rsp.toBitVec original)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (restoredState s original flags, base + 837)) :
    Eventually (step e) P (s, base + 823) := by
  delimited_step 175 using hc
  delimited_step 176 using hc
  delimited_stack_load saved.rbx
  delimited_step 177 using hc
  delimited_stack_load saved.r12
  delimited_step 178 using hc
  delimited_stack_load saved.r13
  delimited_step 179 using hc
  delimited_stack_load saved.r14
  delimited_step 180 using hc
  delimited_stack_load saved.r15
  delimited_step 181 using hc
  delimited_stack_load saved.rbp
  simpa [restoredState, BitVec.add_assoc, BitVec.add_comm, bv_add_left_comm,
    UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc,
    show (8 : UInt64) + 80 = 88 by decide] using hp _

end SszX86.Delimited
