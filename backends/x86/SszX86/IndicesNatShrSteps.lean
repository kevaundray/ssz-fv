import SszX86.IndicesNatShrImpl
import SszX86.DelimitedCore

namespace SszX86.IndicesNatShr
open Kraken.X64.Parser

macro "indices_shr_chunk_step " chunk:ident " row " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member : ($chunk[$k]'(by decide)) ∈ SszX86.IndicesNatShr.program := by
     have selected : ($chunk[$k]'(by decide)) ∈ $chunk := List.getElem_mem (by decide)
     simp only [SszX86.IndicesNatShr.program, List.mem_append]
     simp only [selected, true_or, or_true]
   have fetched := SszX86.IndicesNatShr.step_at _ _ $hc
     ($chunk[$k]'(by decide)) member
   simp only [$chunk, List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.IndicesNatShr.directives, SszX86.IndicesNatShr.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "indices_shr_step " k:num " using " hc:term : tactic => do
  let chunk := Lean.mkIdent
    (if k.getNat < 64 then ``SszX86.IndicesNatShr.programChunk0
     else if k.getNat < 128 then ``SszX86.IndicesNatShr.programChunk1
     else if k.getNat < 192 then ``SszX86.IndicesNatShr.programChunk2
     else ``SszX86.IndicesNatShr.programChunk3)
  let row := Lean.Syntax.mkNumLit (toString (k.getNat % 64))
  `(tactic| indices_shr_chunk_step $chunk row $row using $hc)

macro "indices_shr_load " h:term : tactic => `(tactic|
  simp (config := {instances := true}) [MachineData.load, Width.bytes, Width.bits,
    Effects.All, BitVec.ofInt_add, BitVec.ofInt_toInt, ($h),
    Delimited.word_cast, -Bool.forall_bool])

end SszX86.IndicesNatShr
