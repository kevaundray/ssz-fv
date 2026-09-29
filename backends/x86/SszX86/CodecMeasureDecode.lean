import SszX86.CodecMeasureImpl
import SszX86.DelimitedCore

namespace SszX86.CodecMeasure
open Kraken.X64.Parser
open BoolCodec UintCodec

macro "codec_measure_chunk_member" : tactic => `(tactic|
  (intro row member
   simp only [SszX86.CodecMeasure.program, List.mem_append]
   simp [member]))

theorem chunk0_subset : programChunk0 ⊆ program := by codec_measure_chunk_member
theorem chunk1_subset : programChunk1 ⊆ program := by codec_measure_chunk_member
theorem chunk2_subset : programChunk2 ⊆ program := by codec_measure_chunk_member
theorem chunk3_subset : programChunk3 ⊆ program := by codec_measure_chunk_member
theorem chunk4_subset : programChunk4 ⊆ program := by codec_measure_chunk_member
theorem chunk5_subset : programChunk5 ⊆ program := by codec_measure_chunk_member
theorem chunk6_subset : programChunk6 ⊆ program := by codec_measure_chunk_member
theorem chunk7_subset : programChunk7 ⊆ program := by codec_measure_chunk_member
theorem chunk8_subset : programChunk8 ⊆ program := by codec_measure_chunk_member
theorem chunk9_subset : programChunk9 ⊆ program := by codec_measure_chunk_member
theorem chunk10_subset : programChunk10 ⊆ program := by codec_measure_chunk_member
theorem chunk11_subset : programChunk11 ⊆ program := by codec_measure_chunk_member
theorem chunk12_subset : programChunk12 ⊆ program := by codec_measure_chunk_member

/-- A bounded 64-row fetch certificate prevents accidental normalization of the
whole linked recursive image while preserving each original opcode and width. -/
macro "codec_measure_step " chunk:num " row " row:num " using " code:term : tactic => do
  let source := Lean.mkIdent (Lean.Name.str `SszX86.CodecMeasure s!"programChunk{chunk.getNat}")
  let subset := Lean.mkIdent (Lean.Name.str `SszX86.CodecMeasure s!"chunk{chunk.getNat}_subset")
  `(tactic|
    (apply step_cps
     have member := $subset (List.getElem_mem (l := $source) (n := $row) (by decide))
     have fetched := SszX86.CodecMeasure.step_at _ _ $code _ member
     unfold $source:ident at fetched
     simp only [List.getElem_cons_zero, List.getElem_cons_succ] at fetched
     apply (fetched _ _).mpr
     simp (config := {instances := true})
       [SszX86.CodecMeasure.directives, SszX86.CodecMeasure.labels,
        Directives.interp, Directive.interp, Instr.interp, Operation.interp,
        Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp, ConstExpr.interp,
        RelRegOrMem.interp, BitVec.toAddressSize, MachineData.set, MachineData.setReg,
        Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
        BitVec.drop, BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
        BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
        BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
        Int64.add_assoc, Width.bytesv]))

end SszX86.CodecMeasure
