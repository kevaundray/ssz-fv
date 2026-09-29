import SszX86.CodecEmitPartsImpl
import SszX86.DelimitedCore
import SszX86.NatCompareExec

namespace SszX86.CodecEmitParts
open Kraken.X64.Parser

/-- Select one concrete linked row before reducing its machine interpretation.
No instruction is replaced and all branch labels remain CodeAt obligations. -/
macro "codec_parts_step " row:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member := List.getElem_mem (l := SszX86.CodecEmitParts.program) (n := $row)
     (by rw [SszX86.CodecEmitParts.program_length]; decide)
   have fetched := SszX86.CodecEmitParts.step_at _ _ $hc
     (SszX86.CodecEmitParts.program[$row]'(by
       rw [SszX86.CodecEmitParts.program_length]; decide)) member
   simp only [SszX86.CodecEmitParts.program, SszX86.CodecEmitParts.programChunk0,
     SszX86.CodecEmitParts.programChunk1, SszX86.CodecEmitParts.programChunk2,
     SszX86.CodecEmitParts.programChunk3, List.cons_append, List.nil_append,
     List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecEmitParts.directives, SszX86.CodecEmitParts.labels,
      Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Int64.add_assoc, Width.bytesv]))

macro "codec_parts_load " observation:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Effects.All, ($observation), SszX86.Delimited.word_cast,
      SszX86.Delimited.byte_cast, Width.bytes, Width.bits,
      BitVec.ofInt_add, BitVec.ofInt_toInt])

end SszX86.CodecEmitParts
