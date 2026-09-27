import SszX86.NatAddCore
import SszX86.DelimitedStackMemory

namespace SszX86.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The exact same six SysV saves as the delimited pilot, without local slots. -/
abbrev pushedMem := Delimited.pushedMem
abbrev pushedState := Delimited.pushedState

private theorem activation_load (m : DataMem) (sp : BitVec 64) (off : Nat)
    (hm : UintCodec.Large.Mapped m (sp - 48) 48)
    (low : 8 ≤ off) (high : off ≤ 48) :
    ∃ old, Mem.loadInt m (sp - BitVec.ofNat 64 off) 8 = some old := by
  have address : sp - BitVec.ofNat 64 off =
      (sp - 48) + BitVec.ofNat 64 (48-off) := by bv_omega
  rw [address]
  exact UintCodec.Large.mapped_load m (sp - 48) 48 (48-off) 8 hm (by omega)

macro "natadd_push " row:num " offset " off:num " using " hc:term
    " mapped " hm:term : tactic => `(tactic|
  (natadd_step $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · apply activation_load (off := $off)
     · repeat' first | exact $hm | apply UintCodec.Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

theorem pushes_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : UintCodec.Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (pushedState s, base + 10)) :
    Eventually (step e) P (s, base) := by
  rw [← show base + Int64.ofNat 0 = base by simp]
  natadd_push 0 offset 8 using hc mapped hm
  natadd_push 1 offset 16 using hc mapped hm
  natadd_push 2 offset 24 using hc mapped hm
  natadd_push 3 offset 32 using hc mapped hm
  natadd_push 4 offset 40 using hc mapped hm
  natadd_push 5 offset 48 using hc mapped hm
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 - 8 = s.regs.rsp - 48 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  simpa [pushedState, pushedMem, Delimited.pushedState, Delimited.pushedMem,
    Width.bytesv, BitVec.sub_sub, stackReg] using next

structure SavedAt (m : DataMem) (sp : BitVec 64) (original : MachineData) : Prop where
  rbx : Mem.loadInt m sp 8 = some (original.regs.rbx.toBitVec.toInt.take 64)
  r12 : Mem.loadInt m (sp + 8#64) 8 = some (original.regs.r12.toBitVec.toInt.take 64)
  r13 : Mem.loadInt m (sp + 16#64) 8 = some (original.regs.r13.toBitVec.toInt.take 64)
  r14 : Mem.loadInt m (sp + 24#64) 8 = some (original.regs.r14.toBitVec.toInt.take 64)
  r15 : Mem.loadInt m (sp + 32#64) 8 = some (original.regs.r15.toBitVec.toInt.take 64)
  rbp : Mem.loadInt m (sp + 40#64) 8 = some (original.regs.rbp.toBitVec.toInt.take 64)

theorem pushed_saved (s : MachineData) :
    SavedAt (pushedMem s) (s.regs.rsp.toBitVec - 48) s := by
  have saved := Delimited.pushed_saved s
  have address (a : Nat) (high : a ≤ 40) :
      s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 a =
        s.regs.rsp.toBitVec - 88 + BitVec.ofNat 64 (a+40) := by bv_omega
  constructor
  · rw [show s.regs.rsp.toBitVec - 48 = s.regs.rsp.toBitVec - 88 + 40#64 by bv_omega]
    exact saved.rbx
  · rw [address 8 (by decide)]
    exact saved.r12
  · rw [address 16 (by decide)]
    exact saved.r13
  · rw [address 24 (by decide)]
    exact saved.r14
  · rw [address 32 (by decide)]
    exact saved.r15
  · rw [address 40 (by decide)]
    exact saved.rbp

def restoredState (s original : MachineData) : MachineData :=
  {s with regs := {s.regs with
    rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 48)
    rbx := original.regs.rbx
    rbp := original.regs.rbp
    r12 := original.regs.r12
    r13 := original.regs.r13
    r14 := original.regs.r14
    r15 := original.regs.r15}}

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "natadd_stack_load " hw:term : tactic => `(tactic|
  simp [MachineData.load, Effects.All, ($hw), Delimited.take_cast,
    BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
    UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc])

theorem restore_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s original : MachineData) (saved : SavedAt s.dmem s.regs.rsp.toBitVec original)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (restoredState s original, base + 622)) :
    Eventually (step e) P (s, base + 612) := by
  natadd_step 158 using hc
  natadd_stack_load saved.rbx
  natadd_step 159 using hc
  natadd_stack_load saved.r12
  natadd_step 160 using hc
  natadd_stack_load saved.r13
  natadd_step 161 using hc
  natadd_stack_load saved.r14
  natadd_step 162 using hc
  natadd_stack_load saved.r15
  natadd_step 163 using hc
  natadd_stack_load saved.rbp
  simpa [restoredState, BitVec.add_assoc, BitVec.add_comm, bv_add_left_comm,
    UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc,
    show (8 : UInt64) + 40 = 48 by decide] using next

theorem ret_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (post : P (Delimited.retState s, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 622) := by
  natadd_step 164 using hc
  simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
  exact Eventually.done _ post

end SszX86.NatAdd
