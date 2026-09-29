import SszX86.IndicesCeilShiftImpl
import SszX86.DelimitedCore

namespace SszX86.IndicesCeilShift
open Kraken.X64.Parser

macro "indices_ceil_chunk_step " chunk:ident " row " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member : ($chunk[$k]'(by decide)) ∈ SszX86.IndicesCeilShift.program := by
     have selected : ($chunk[$k]'(by decide)) ∈ $chunk := List.getElem_mem (by decide)
     simp only [SszX86.IndicesCeilShift.program, List.mem_append]
     simp only [selected, true_or, or_true]
   have fetched := SszX86.IndicesCeilShift.step_at _ _ $hc
     ($chunk[$k]'(by decide)) member
   simp only [$chunk, List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.IndicesCeilShift.directives, SszX86.IndicesCeilShift.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "indices_ceil_step " k:num " using " hc:term : tactic => do
  let chunk := Lean.mkIdent
    (if k.getNat < 64 then ``SszX86.IndicesCeilShift.programChunk0
     else if k.getNat < 128 then ``SszX86.IndicesCeilShift.programChunk1
     else if k.getNat < 192 then ``SszX86.IndicesCeilShift.programChunk2
     else if k.getNat < 256 then ``SszX86.IndicesCeilShift.programChunk3
     else if k.getNat < 320 then ``SszX86.IndicesCeilShift.programChunk4
     else ``SszX86.IndicesCeilShift.programChunk5)
  let row := Lean.Syntax.mkNumLit (toString (k.getNat % 64))
  `(tactic| indices_ceil_chunk_step $chunk row $row using $hc)

end SszX86.IndicesCeilShift
