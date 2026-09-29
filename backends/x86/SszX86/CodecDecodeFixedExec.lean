import SszX86.CodecDecodeFixedImpl
import SszX86.CodecDeserializeWords
import SszX86.DelimitedCore

set_option autoImplicit false

namespace SszX86.CodecDecodeFixed
open Kraken.X64.Parser
open SszNative UintCodec

macro "codec_fixed_core_step " chunk:ident " row " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member : ($chunk[$k]'(by decide)) ∈ SszX86.CodecDecodeFixed.program := by
     have selected : ($chunk[$k]'(by decide)) ∈ $chunk := List.getElem_mem (by decide)
     simp only [SszX86.CodecDecodeFixed.program, List.mem_append]
     simp only [selected, true_or, or_true]
   have fetched := SszX86.CodecDecodeFixed.step_at _ _ $hc
     ($chunk[$k]'(by decide)) member
   simp only [$chunk, List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecDecodeFixed.directives, SszX86.CodecDecodeFixed.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "codec_fixed_core_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast])

end SszX86.CodecDecodeFixed
