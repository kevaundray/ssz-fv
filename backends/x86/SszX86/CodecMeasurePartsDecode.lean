import SszX86.CodecMeasurePartsImpl
import SszX86.DelimitedCore

namespace SszX86.CodecMeasureParts
open Kraken.X64.Parser
open BoolCodec UintCodec

macro "codec_measure_parts_step " row:num " using " code:term : tactic => do
  let source := Lean.mkIdent
    (Lean.Name.str `SszX86.CodecMeasureParts s!"programChunk{row.getNat / 64}")
  let index := Lean.quote (row.getNat % 64)
  `(tactic|
    (apply step_cps
     have item := List.getElem_mem (l := $source) (n := $index) (by decide)
     have member : ($source[$index]'(by decide)) ∈ SszX86.CodecMeasureParts.program := by
       simp only [SszX86.CodecMeasureParts.program, List.mem_append]
       simp [item]
     have fetched := SszX86.CodecMeasureParts.step_at _ _ $code _ member
     unfold $source:ident at fetched
     simp only [List.getElem_cons_zero, List.getElem_cons_succ] at fetched
     apply (fetched _ _).mpr
     simp (config := {instances := true})
       [SszX86.CodecMeasureParts.directives, SszX86.CodecMeasureParts.labels,
        Directives.interp, Directive.interp, Instr.interp, Operation.interp,
        Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp, ConstExpr.interp,
        RelRegOrMem.interp, BitVec.toAddressSize, MachineData.set, MachineData.setReg,
        Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
        BitVec.drop, BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
        BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
        BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
        Int64.add_assoc, Width.bytesv]))

macro "codec_measure_parts_load " loaded:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($loaded), Delimited.word_cast])

end SszX86.CodecMeasureParts
