import SszX86.IndicesPrefixEqualImpl
import SszX86.DelimitedCore

namespace SszX86.IndicesPrefixEqual
open Kraken.X64.Parser

macro "indices_prefix_chunk_step " chunk:ident " row " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member : ($chunk[$k]'(by decide)) ∈ SszX86.IndicesPrefixEqual.program := by
     have selected : ($chunk[$k]'(by decide)) ∈ $chunk := List.getElem_mem (by decide)
     simp only [SszX86.IndicesPrefixEqual.program, List.mem_append]
     simp only [selected, true_or, or_true]
   have fetched := SszX86.IndicesPrefixEqual.step_at _ _ $hc
     ($chunk[$k]'(by decide)) member
   simp only [$chunk, List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.IndicesPrefixEqual.directives, SszX86.IndicesPrefixEqual.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "indices_prefix_step " k:num " using " hc:term : tactic => do
  let chunk := Lean.mkIdent
    (if k.getNat < 64 then ``SszX86.IndicesPrefixEqual.programChunk0
     else if k.getNat < 128 then ``SszX86.IndicesPrefixEqual.programChunk1
     else if k.getNat < 192 then ``SszX86.IndicesPrefixEqual.programChunk2
     else if k.getNat < 256 then ``SszX86.IndicesPrefixEqual.programChunk3
     else if k.getNat < 320 then ``SszX86.IndicesPrefixEqual.programChunk4
     else ``SszX86.IndicesPrefixEqual.programChunk5)
  let row := Lean.Syntax.mkNumLit (toString (k.getNat % 64))
  `(tactic| indices_prefix_chunk_step $chunk row $row using $hc)

macro "indices_prefix_load " h:term : tactic => `(tactic|
  simp (config := {instances := true}) [MachineData.load, Width.bytes, Width.bits,
    Effects.All, BitVec.ofInt_add, BitVec.ofInt_toInt, ($h),
    Delimited.word_cast, -Bool.forall_bool])

end SszX86.IndicesPrefixEqual
