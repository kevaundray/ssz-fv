import SszX86.BitVectorImpl
import SszX86.NatDivisionProofs
import SszX86.NatAddProofs
import SszX86.NatExactProofs
import SszX86.NatToU128Proofs
import SszBitVectorMemory

namespace SszX86.BitVector
open Kraken.X64.Parser
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Every call target is part of the same real linked executable. -/
structure JointCodeAt (e : Executable) (base : Int64) : Prop where
  body : CodeAt e base
  division : NatDivision.CodeAt e (base + Int64.ofInt divisionOffset)
  udiv : Udivti3.Embedded.CodeAt e
    (base + Int64.ofInt divisionOffset + Int64.ofNat NatDivision.udivOffset)
  add : NatAdd.CodeAt e (base + Int64.ofInt addOffset)
  exact : NatExact.CodeAt e (base + Int64.ofInt exactOffset)
  toU128 : NatToU128.CodeAt e (base + Int64.ofInt toU128Offset)

macro "bitvector_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.BitVector.step_at _ _ $hc
     (SszX86.BitVector.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.BitVector.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.BitVector.program, SszX86.BitVector.directives,
      SszX86.BitVector.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "bitvector_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast])

/-- A finite block summary. The continuation receives only the block's effects,
not its expanded register-update expression. -/
structure Fixed (s t : MachineData) : Prop where
  stack : t.regs.rsp = s.regs.rsp
  arena : t.regs.rbx = s.regs.rbx
  length : t.regs.r14 = s.regs.r14
  pointer : t.regs.r15 = s.regs.r15
  payload : t.regs.r12 = s.regs.r12
  vectors : t.zmms = s.zmms

abbrev callState := NatDivision.callState

/-- The ordinary CALL return slot is below the post-dispatch stack pointer. -/
abbrev CallSlot (s : MachineData) : Prop :=
  ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 = some old

end SszX86.BitVector
