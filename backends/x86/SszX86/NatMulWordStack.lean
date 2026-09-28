import SszX86.NatMulWordCore
import SszX86.NatAddStack

namespace SszX86.NatMulWord

abbrev pushedMem := NatAdd.pushedMem
abbrev SavedAt := NatAdd.SavedAt

def pushedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 64)}
    status := flags
    dmem := pushedMem s}

private theorem activation_load (m : DataMem) (sp : BitVec 64) (off : Nat)
    (hm : UintCodec.Large.Mapped m (sp - 64) 64)
    (low : 8 ≤ off) (high : off ≤ 48) :
    ∃ old, Mem.loadInt m (sp - BitVec.ofNat 64 off) 8 = some old := by
  have address : sp - BitVec.ofNat 64 off =
      (sp - 64) + BitVec.ofNat 64 (64-off) := by bv_omega
  rw [address]
  exact UintCodec.Large.mapped_load m (sp - 64) 64 (64-off) 8 hm (by omega)

macro "natmulword_push " chunk:num ":" row:num " offset " off:num " using " hc:term
    " mapped " hm:term : tactic => `(tactic|
  (natmulword_step $chunk : $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · apply activation_load (off := $off)
     · repeat' first | exact $hm | apply UintCodec.Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

theorem pushes_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : UintCodec.Large.Mapped s.dmem (s.regs.rsp.toBitVec - 64) 64)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (pushedState s flags, base + 113)) :
    Eventually (step e) P (s, base + 99) := by
  natmulword_push 0:27 offset 8 using hc mapped hm
  natmulword_push 0:28 offset 16 using hc mapped hm
  natmulword_push 0:29 offset 24 using hc mapped hm
  natmulword_push 0:30 offset 32 using hc mapped hm
  natmulword_push 0:31 offset 40 using hc mapped hm
  natmulword_push 1:0 offset 48 using hc mapped hm
  natmulword_step 1:1 using hc
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 16 =
      UInt64.ofBitVec (s.regs.rsp.toBitVec - 64) := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  simpa [pushedState, pushedMem, NatAdd.pushedMem, Delimited.pushedMem,
    Width.bytesv, BitVec.sub_sub, stackReg] using next _

theorem pushed_saved (s : MachineData) :
    SavedAt (pushedMem s) (s.regs.rsp.toBitVec - 64 + 16) s := by
  have address : s.regs.rsp.toBitVec - 64 + 16 = s.regs.rsp.toBitVec - 48 := by bv_omega
  rw [address]
  exact NatAdd.pushed_saved s

def restoredState (s original : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 64)
      rbx := original.regs.rbx
      rbp := original.regs.rbp
      r12 := original.regs.r12
      r13 := original.regs.r13
      r14 := original.regs.r14
      r15 := original.regs.r15}
    status := flags}

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "natmulword_stack_load " hw:term : tactic => `(tactic|
  simp [MachineData.load, Effects.All, ($hw), Delimited.take_cast,
    BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
    UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc])

theorem restore_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s original : MachineData) (saved : SavedAt s.dmem (s.regs.rsp.toBitVec + 16) original)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (restoredState s original flags, base + 701)) :
    Eventually (step e) P (s, base + 687) := by
  change SavedAt s.dmem (s.regs.rsp.toBitVec + 16#64) original at saved
  have h12 := saved.r12
  have h13 := saved.r13
  have h14 := saved.r14
  have h15 := saved.r15
  have hbp := saved.rbp
  simp only [BitVec.add_assoc, show 16#64 + 8#64 = 24#64 by decide] at h12
  simp only [BitVec.add_assoc, show 16#64 + 16#64 = 32#64 by decide] at h13
  simp only [BitVec.add_assoc, show 16#64 + 24#64 = 40#64 by decide] at h14
  simp only [BitVec.add_assoc, show 16#64 + 32#64 = 48#64 by decide] at h15
  simp only [BitVec.add_assoc, show 16#64 + 40#64 = 56#64 by decide] at hbp
  natmulword_step 5:14 using hc
  natmulword_step 5:15 using hc
  natmulword_stack_load saved.rbx
  natmulword_step 5:16 using hc
  natmulword_stack_load h12
  natmulword_step 5:17 using hc
  natmulword_stack_load h13
  natmulword_step 5:18 using hc
  natmulword_stack_load h14
  natmulword_step 5:19 using hc
  natmulword_stack_load h15
  natmulword_step 5:20 using hc
  natmulword_stack_load hbp
  simpa [restoredState, BitVec.add_assoc, BitVec.add_comm, bv_add_left_comm,
    UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc,
    show (8 : UInt64) + 56 = 64 by decide] using next _

end SszX86.NatMulWord
