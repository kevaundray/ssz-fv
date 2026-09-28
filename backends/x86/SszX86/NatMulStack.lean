import SszX86.NatMulCore
import SszX86.NatAddStack

namespace SszX86.NatMul

abbrev pushedMem := NatAdd.pushedMem
abbrev pushedState := NatAdd.pushedState
abbrev SavedAt := NatAdd.SavedAt
abbrev restoredState := NatAdd.restoredState

private theorem activation_load (m : DataMem) (sp : BitVec 64) (off : Nat)
    (hm : UintCodec.Large.Mapped m (sp - 48) 48)
    (low : 8 ≤ off) (high : off ≤ 48) :
    ∃ old, Mem.loadInt m (sp - BitVec.ofNat 64 off) 8 = some old := by
  have address : sp - BitVec.ofNat 64 off =
      (sp - 48) + BitVec.ofNat 64 (48-off) := by bv_omega
  rw [address]
  exact UintCodec.Large.mapped_load m (sp - 48) 48 (48-off) 8 hm (by omega)

macro "natmul_push " row:num " offset " off:num " using " hc:term
    " mapped " hm:term : tactic => `(tactic|
  (natmul_step 0 row $row using $hc
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
  natmul_push 0 offset 8 using hc mapped hm
  natmul_push 1 offset 16 using hc mapped hm
  natmul_push 2 offset 24 using hc mapped hm
  natmul_push 3 offset 32 using hc mapped hm
  natmul_push 4 offset 40 using hc mapped hm
  natmul_push 5 offset 48 using hc mapped hm
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 - 8 = s.regs.rsp - 48 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  simpa [pushedState, pushedMem, NatAdd.pushedState, NatAdd.pushedMem,
    Delimited.pushedState, Delimited.pushedMem,
    Width.bytesv, BitVec.sub_sub, stackReg] using next

def localState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rsp := s.regs.rsp - 40}, status := flags}

theorem locals_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (localState s flags, base + 14)) :
    Eventually (step e) P (s, base + 10) := by
  natmul_step 0 row 6 using hc
  simpa [localState] using next _

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "natmul_stack_load " hw:term : tactic => `(tactic|
  simp [MachineData.load, Effects.All, ($hw), Delimited.take_cast,
    BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
    UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc])

theorem restore_return_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s original : MachineData) (saved : SavedAt s.dmem s.regs.rsp.toBitVec original)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (restoredState s original, base + 242)) :
    Eventually (step e) P (s, base + 232) := by
  natmul_step 2 row 11 using hc
  natmul_stack_load saved.rbx
  natmul_step 2 row 12 using hc
  natmul_stack_load saved.r12
  natmul_step 2 row 13 using hc
  natmul_stack_load saved.r13
  natmul_step 2 row 14 using hc
  natmul_stack_load saved.r14
  natmul_step 2 row 15 using hc
  natmul_stack_load saved.r15
  natmul_step 2 row 16 using hc
  natmul_stack_load saved.rbp
  simpa [restoredState, NatAdd.restoredState, BitVec.add_assoc, BitVec.add_comm, bv_add_left_comm,
    UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc,
    show (8 : UInt64) + 40 = 48 by decide] using next

theorem restore_tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s original : MachineData) (saved : SavedAt s.dmem s.regs.rsp.toBitVec original)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (restoredState s original, base + 201)) :
    Eventually (step e) P (s, base + 191) := by
  natmul_step 2 row 0 using hc
  natmul_stack_load saved.rbx
  natmul_step 2 row 1 using hc
  natmul_stack_load saved.r12
  natmul_step 2 row 2 using hc
  natmul_stack_load saved.r13
  natmul_step 2 row 3 using hc
  natmul_stack_load saved.r14
  natmul_step 2 row 4 using hc
  natmul_stack_load saved.r15
  natmul_step 2 row 5 using hc
  natmul_stack_load saved.rbp
  simpa [restoredState, NatAdd.restoredState, BitVec.add_assoc, BitVec.add_comm, bv_add_left_comm,
    UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc,
    show (8 : UInt64) + 40 = 48 by decide] using next

def unlocalState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rsp := s.regs.rsp + 40}, status := flags}

theorem unlocal_return_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (unlocalState s flags, base + 232)) :
    Eventually (step e) P (s, base + 228) := by
  natmul_step 2 row 10 using hc
  simpa [unlocalState, UInt64.add_comm] using next _

theorem unlocal_tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (unlocalState s flags, base + 191)) :
    Eventually (step e) P (s, base + 187) := by
  natmul_step 1 row 31 using hc
  simpa [unlocalState, UInt64.add_comm] using next _

theorem ret_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (post : P (Delimited.retState s, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 242) := by
  natmul_step 2 row 17 using hc
  simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
  exact Eventually.done _ post

theorem word_tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (s, base + Int64.ofNat wordOffset)) :
    Eventually (step e) P (s, base + 201) := by
  natmul_step 2 row 6 using hc
  simpa [wordOffset] using next

end SszX86.NatMul
