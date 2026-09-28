import SszX86.NatMulWordImpl
import SszX86.NatAddCore
import SszX86.DelimitedMemory
import SszNatMul

namespace SszX86.NatMulWord
open Kraken.X64.Parser
open UintCodec

macro "natmulword_step " chunk:num ":" row:num " using " hc:term : tactic => do
  let name := Lean.mkIdent (Lean.Name.str `SszX86.NatMulWord s!"programChunk{chunk.getNat}")
  `(tactic|
    (apply step_cps
     have member := List.getElem_mem (l := $name) (n := $row) (by decide)
     have included : ($name[$row]'(by decide)) ∈ SszX86.NatMulWord.program := by
       simp only [SszX86.NatMulWord.program, List.mem_append, member, or_true, true_or]
     have fetched := SszX86.NatMulWord.step_at _ _ $hc
       ($name[$row]'(by decide)) included
     unfold $name:ident at fetched
     simp only [List.getElem_cons_zero, List.getElem_cons_succ] at fetched
     apply (fetched _ _).mpr
     simp (config := {instances := true})
       [SszX86.NatMulWord.directives, SszX86.NatMulWord.usedLabels,
        Directives.interp, Directive.interp, Instr.interp, Operation.interp,
        Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
        ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
        MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
        Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
        BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
        BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
        Int64.add_assoc, Width.bytes, Width.bits]))

macro "natmulword_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast])

abbrev OutputMapped (s : MachineData) : Prop :=
  Large.Mapped s.dmem s.regs.rdi.toBitVec 72

macro "natmulword_output " chunk:num ":" row:num " at " offset:num
    " width " byteCount:num " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 72) (byteCount := $byteCount))
  else
    `(tactic| apply Large.mapped_load (capacity := 72)
      (offset := $offset) («width» := $byteCount))
  `(tactic|
    (natmulword_step $chunk : $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply Large.mapped_store
       · decide
     simp only [Effects.All]))

end SszX86.NatMulWord
