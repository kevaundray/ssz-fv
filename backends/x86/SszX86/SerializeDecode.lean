import SszX86.SerializeImpl
import SszX86.MeasureBorrowed
import SszX86.MeasureObservations
import SszX86.MeasurePadding
import SszX86.EmitProofs

namespace SszX86.Serialize
open Kraken.X64.Parser
open BoolCodec UintCodec

abbrev step (e : Executable) := BoolCodec.step e

theorem step_at (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ program)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  simp only [step, BoolCodec.step, step1, Executable.step, hc.fetch row hr]

macro "serialize_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.Serialize.step_at _ _ $hc
     (SszX86.Serialize.program[$k]'(by rw [SszX86.Serialize.program_length]; decide))
     (List.getElem_mem (by rw [SszX86.Serialize.program_length]; decide))
   simp only [SszX86.Serialize.program, SszX86.Serialize.programChunk0,
     SszX86.Serialize.programChunk1, List.append_cons, List.nil_append,
     List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.Serialize.directives, SszX86.Serialize.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp, ConstExpr.interp,
      RelRegOrMem.interp, BitVec.toAddressSize, MachineData.set, MachineData.setReg,
      Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
      BitVec.drop, BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Int64.add_assoc, Width.bytesv]))

macro "serialize_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast])

theorem ClosureAt.measure_helpers {e : Executable} {base : Int64}
    (closure : ClosureAt e base) :
    Measure.HelpersAt e (base + Int64.ofInt measureOffset) := by
  refine ⟨?_, ?_⟩
  · simpa only [measureOffset, Measure.compareOffset, compareOffset, Int64.add_assoc,
      show Int64.ofInt (-33488) + Int64.ofInt (-32880) = Int64.ofInt (-66368) by decide]
      using closure.compare
  · simpa only [measureOffset, Measure.fromU128Offset, fromU128Offset, Int64.add_assoc,
      show Int64.ofInt (-33488) + Int64.ofInt (-14704) = Int64.ofInt (-48192) by decide]
      using closure.fromU128

theorem ClosureAt.emit_memcpy {e : Executable} {base : Int64}
    (closure : ClosureAt e base) :
    Emit.MemcpyCodeAt e ((base + Int64.ofInt emitOffset) + 110736) := by
  simpa only [emitOffset, memcpyOffset, Int64.add_assoc,
    show Int64.ofInt (-29952) + 110736 = Int64.ofInt 80784 by decide] using closure.memcpy

end SszX86.Serialize
