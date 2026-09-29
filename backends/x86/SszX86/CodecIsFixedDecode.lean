import SszX86.CodecIsFixedImpl
import SszX86.DelimitedCore

namespace SszX86.CodecIsFixed
open Kraken.X64.Parser
open BoolCodec UintCodec

/-- Reduce one fetched instruction only; CALL remains the real stack-writing
machine instruction, never a semantic recursive-call oracle. -/
macro "codec_is_fixed_step " row:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.CodecIsFixed.step_at _ _ $hc
     (SszX86.CodecIsFixed.program[$row]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.CodecIsFixed.program, SszX86.CodecIsFixed.programChunk0,
     List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecIsFixed.directives, SszX86.CodecIsFixed.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp, ConstExpr.interp,
      RelRegOrMem.interp, BitVec.toAddressSize, MachineData.set, MachineData.setReg,
      Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
      BitVec.drop, BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Int64.add_assoc, Width.bytesv]))

macro "codec_is_fixed_load " loaded:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($loaded), Delimited.word_cast])

end SszX86.CodecIsFixed
