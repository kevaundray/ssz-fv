import SszX86.DispatchTable
import SszX86.BoolExec
import SszX86.UintLimbMemory
import SszX86.DelimitedCore

namespace SszX86.Dispatch
open BoolCodec UintCodec

abbrev step (e : Executable) := BoolCodec.step e

macro "dispatch_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.Dispatch.step_at _ _ $hc
     (SszX86.Dispatch.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.Dispatch.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.Dispatch.directives, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, Int64.add_assoc, Width.bytesv]))

def savedMem (s : MachineData) : DataMem :=
  Mem.storeInt (Mem.storeInt (Mem.storeInt (Mem.storeInt (Mem.storeInt
    (Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 s.regs.rbp.toBitVec.toInt)
      (s.regs.rsp.toBitVec - 16) 8 s.regs.r15.toBitVec.toInt)
      (s.regs.rsp.toBitVec - 24) 8 s.regs.r14.toBitVec.toInt)
      (s.regs.rsp.toBitVec - 32) 8 s.regs.r13.toBitVec.toInt)
      (s.regs.rsp.toBitVec - 40) 8 s.regs.r12.toBitVec.toInt)
      (s.regs.rsp.toBitVec - 48) 8 s.regs.rbx.toBitVec.toInt

def savedState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 48)}
    dmem := savedMem s}

theorem push_load (m : DataMem) (sp : BitVec 64) (offset : Nat)
    (hm : Large.Mapped m (sp - 48) 48) (lo : 8 ≤ offset) (hi : offset ≤ 48) :
    ∃ old, Mem.loadInt m (sp - BitVec.ofNat 64 offset) 8 = some old := by
  have addr : sp - BitVec.ofNat 64 offset = (sp - 48) + BitVec.ofNat 64 (48 - offset) := by
    bv_omega
  rw [addr]
  exact Large.mapped_load m (sp - 48) 48 (48 - offset) 8 hm (by omega)

macro "dispatch_push " row:num ", " off:num " using " hc:term
    ", " hm:term : tactic => `(tactic|
  (dispatch_step $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · have hm' := $hm
     apply SszX86.Dispatch.push_load (offset := $off)
     · repeat' first | exact hm' | apply Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

/-- The six actual PUSH instructions install the callee-saved words. Their old
contents are arbitrary, but the writable stack bytes must already be mapped. -/
theorem pushes_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (next : Eventually (step e) P (savedState s, base + 10)) :
    Eventually (step e) P (s, base) := by
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 - 8 = s.regs.rsp - 48 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  suffices run : Eventually (step e) P (s, base + 0) by
    simpa only [Int64.add_zero] using run
  dispatch_push 0, 8 using hc, hm
  dispatch_push 1, 16 using hc, hm
  dispatch_push 2, 24 using hc, hm
  dispatch_push 3, 32 using hc, hm
  dispatch_push 4, 40 using hc, hm
  dispatch_push 5, 48 using hc, hm
  simpa [savedState, savedMem, Width.bytesv, BitVec.sub_sub, stackReg] using next

end SszX86.Dispatch
