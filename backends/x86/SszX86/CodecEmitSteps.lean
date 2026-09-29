import SszX86.CodecEmitImpl
import SszX86.DelimitedCore
import SszX86.NatCompareExec

namespace SszX86.CodecEmit
open Kraken.X64.Parser

theorem programChunk0_member {row : Nat × Nat × Program} (h : row ∈ programChunk0) :
    row ∈ program := by
  simp only [program, List.mem_append, h, or_true, true_or]

theorem programChunk1_member {row : Nat × Nat × Program} (h : row ∈ programChunk1) :
    row ∈ program := by
  simp only [program, List.mem_append, h, or_true, true_or]

theorem programChunk2_member {row : Nat × Nat × Program} (h : row ∈ programChunk2) :
    row ∈ program := by
  simp only [program, List.mem_append, h, or_true, true_or]

theorem programChunk3_member {row : Nat × Nat × Program} (h : row ∈ programChunk3) :
    row ∈ program := by
  simp only [program, List.mem_append, h, or_true, true_or]

theorem programChunk4_member {row : Nat × Nat × Program} (h : row ∈ programChunk4) :
    row ∈ program := by
  simp only [program, List.mem_append, h, or_true, true_or]

theorem programChunk5_member {row : Nat × Nat × Program} (h : row ∈ programChunk5) :
    row ∈ program := by
  simp only [program, List.mem_append, h, or_true, true_or]

theorem programChunk6_member {row : Nat × Nat × Program} (h : row ∈ programChunk6) :
    row ∈ program := by
  simp only [program, List.mem_append, h, or_true, true_or]

macro "codec_emit_step " row:num " using " hc:term : tactic => do
  let chunk ← match row.getNat / 64 with
    | 0 => `(term| SszX86.CodecEmit.programChunk0)
    | 1 => `(term| SszX86.CodecEmit.programChunk1)
    | 2 => `(term| SszX86.CodecEmit.programChunk2)
    | 3 => `(term| SszX86.CodecEmit.programChunk3)
    | 4 => `(term| SszX86.CodecEmit.programChunk4)
    | 5 => `(term| SszX86.CodecEmit.programChunk5)
    | 6 => `(term| SszX86.CodecEmit.programChunk6)
    | _ => Lean.Macro.throwErrorAt row "emit row outside the linked image"
  let membership ← match row.getNat / 64 with
    | 0 => `(term| SszX86.CodecEmit.programChunk0_member)
    | 1 => `(term| SszX86.CodecEmit.programChunk1_member)
    | 2 => `(term| SszX86.CodecEmit.programChunk2_member)
    | 3 => `(term| SszX86.CodecEmit.programChunk3_member)
    | 4 => `(term| SszX86.CodecEmit.programChunk4_member)
    | 5 => `(term| SszX86.CodecEmit.programChunk5_member)
    | 6 => `(term| SszX86.CodecEmit.programChunk6_member)
    | _ => Lean.Macro.throwErrorAt row "emit row outside the linked image"
  return ← `(tactic|
  (apply step_cps
   have member := List.getElem_mem (l := $chunk) (n := $row % 64) (by decide)
   have fetched := SszX86.CodecEmit.step_at _ _ $hc
     (($chunk)[$row % 64]'(by decide)) ($membership member)
   simp only [$chunk, Nat.reduceMod, List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecEmit.directives, SszX86.CodecEmit.labels,
      Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Int64.add_assoc, Width.bytesv]))

macro "codec_emit_load " observation:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Effects.All, ($observation), SszX86.Delimited.word_cast,
      SszX86.Delimited.byte_cast, Width.bytes, Width.bits,
      BitVec.ofInt_add, BitVec.ofInt_toInt])

end SszX86.CodecEmit
