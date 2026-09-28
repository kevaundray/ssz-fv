import SszX86.NatMulLoopMultiply
import SszX86.NatMulWordMath

namespace SszX86.NatMul.Product
open SszNative

/-- Registers untouched by all instructions of the inner loop. -/
structure InnerStable (s t : MachineData) : Prop where
  rsi : t.regs.rsi = s.regs.rsi
  rcx : t.regs.rcx = s.regs.rcx
  r10 : t.regs.r10 = s.regs.r10
  r11 : t.regs.r11 = s.regs.r11
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15
  rbp : t.regs.rbp = s.regs.rbp
  rsp : t.regs.rsp = s.regs.rsp
  zmms : t.zmms = s.zmms

theorem InnerStable.refl (s : MachineData) : InnerStable s s :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem InnerStable.trans {a b c : MachineData} (ab : InnerStable a b) (bc : InnerStable b c) :
    InnerStable a c :=
  ⟨bc.rsi.trans ab.rsi, bc.rcx.trans ab.rcx, bc.r10.trans ab.r10,
    bc.r11.trans ab.r11, bc.r12.trans ab.r12, bc.r13.trans ab.r13,
    bc.r14.trans ab.r14, bc.r15.trans ab.r15, bc.rbp.trans ab.rbp,
    bc.rsp.trans ab.rsp, bc.zmms.trans ab.zmms⟩

/-- One bounded original iteration realizes exactly the checked limb recurrence. -/
theorem inner_step_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (word old : BitVec 64) (carry : Nat) (carryBound : carry < 2^64)
    (carryReg : s.regs.r9.toBitVec = BitVec.ofNat 64 carry) (zeroHigh : s.regs.r8 = 0)
    (inside : (s.regs.r15.toBitVec + s.regs.rbx.toBitVec).toNat < s.regs.r14.toBitVec.toNat)
    (wordLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + s.regs.rbx.toBitVec * 8#64) 8 =
      some (word.toNat : Int))
    (oldLoad : Mem.loadInt s.dmem (s.regs.r10.toBitVec + s.regs.rbx.toBitVec * 8#64) 8 =
      some (old.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ t, InnerStable s t →
      t.regs.rbx.toBitVec = s.regs.rbx.toBitVec + 1 →
      t.regs.r9.toBitVec = BitVec.ofNat 64 (LimbMul.step s.regs.rcx.toBitVec word old carry).2 →
      t.regs.r8 = 0 →
      t.dmem = Mem.storeInt s.dmem (s.regs.r10.toBitVec + s.regs.rbx.toBitVec * 8#64)
        8 (LimbMul.step s.regs.rcx.toBitVec word old carry).1.toInt →
      Eventually (step e) P (t,
        if s.regs.rbx.toBitVec + 1 = s.regs.r13.toBitVec then base + 627 else base + 576)) :
    Eventually (step e) P (s, base + 576) := by
  have arithmetic := NatMulWord.add_carry_step s.regs.rcx.toBitVec word old carry carryBound
  apply guard_cps e base hc s inside P
  intro guardFlags
  apply multiply_cps e base hc _ word wordLoad P
  intro mulFlags
  apply add_carry_cps e base hc _ zeroHigh P
  intro carryFlags
  apply update_cps e base hc _ old oldLoad P
  intro updateFlags
  apply advance_cps e base hc _ P
  intro advanceFlags
  apply next
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · rfl
  · simpa [advancedState, updatedState, updatedCarry, carriedState, carriedHigh,
      carriedLow, multipliedState, guardedState, carryReg, rawHigh, NatMulWord.productHigh,
      Udivti3.addFlags_cf, Nat.add_comm, BitVec.add_comm] using arithmetic.2
  · rfl
  · have low : updatedWord
        (carriedState (multipliedState (guardedState s guardFlags) word mulFlags) carryFlags) old =
        (LimbMul.step s.regs.rcx.toBitVec word old carry).1 := by
      simpa [updatedWord, carriedState, carriedLow, multipliedState, guardedState,
        carryReg, BitVec.add_comm] using arithmetic.1
    simpa [advancedState, updatedState, carriedState, multipliedState, guardedState, low]

end SszX86.NatMul.Product
