import SszX86.IndicesChunkCountImpl
import SszX86.CodecPlanSingletonMemory
import SszX86.NatCompareExec
import SszIndicesPaths

namespace SszX86.IndicesChunkCount
open Kraken.X64.Parser
open SszNative UintCodec

macro "indices_count_chunk_step " chunk:ident " row " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member : ($chunk[$k]'(by decide)) ∈ SszX86.IndicesChunkCount.program := by
     have selected : ($chunk[$k]'(by decide)) ∈ $chunk := List.getElem_mem (by decide)
     simp only [SszX86.IndicesChunkCount.program, List.mem_append]
     simp only [selected, true_or, or_true]
   have fetched := SszX86.IndicesChunkCount.step_at _ _ $hc
     ($chunk[$k]'(by decide)) member
   simp only [$chunk, List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.IndicesChunkCount.directives, SszX86.IndicesChunkCount.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bytesv, Width.bits]))

macro "indices_count_step " k:num " using " hc:term : tactic => do
  let chunk := Lean.mkIdent
    (if k.getNat < 64 then ``SszX86.IndicesChunkCount.programChunk0
     else if k.getNat < 128 then ``SszX86.IndicesChunkCount.programChunk1
     else ``SszX86.IndicesChunkCount.programChunk2)
  let row := Lean.Syntax.mkNumLit (toString (k.getNat % 64))
  `(tactic| indices_count_chunk_step $chunk row $row using $hc)

macro "indices_count_load " observation:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($observation), NatCompare.word_cast])

/-- Each cut describes one real original instruction; flags remain opaque. -/
def tagged (s : MachineData) (tag : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec tag}}

theorem tag_load_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (tag : BitVec 64)
    (loaded : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (tag.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (tagged s tag, base + 10)) :
    Eventually (step e) P (s, base + 7) := by
  indices_count_step 3 using code
  indices_count_load loaded
  simpa only [tagged] using next

/-- The compiler guard admits every physical Desc tag, including malformed
metadata. It is not a schema-validity check. -/
theorem tag_guard_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (tag : Fin 13) (inRax : s.regs.rax = UInt64.ofNat tag.val)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 16)) :
    Eventually (step e) P (s, base + 10) := by
  have choices : tag.val = 0 ∨ tag.val = 1 ∨ tag.val = 2 ∨ tag.val = 3 ∨
      tag.val = 4 ∨ tag.val = 5 ∨ tag.val = 6 ∨ tag.val = 7 ∨ tag.val = 8 ∨
      tag.val = 9 ∨ tag.val = 10 ∨ tag.val = 11 ∨ tag.val = 12 := by
    have := tag.isLt
    omega
  indices_count_step 4 using code
  indices_count_step 5 using code
  rcases choices with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simpa [inRax, h, StatusFlags.from_result, NatCompare.cf_sub,
      Effects.All] using next _

def arenaSaved (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rbx := s.regs.rdx}}

theorem arena_save_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (arenaSaved s, base + 19)) :
    Eventually (step e) P (s, base + 16) := by
  indices_count_step 6 using code
  simpa only [arenaSaved] using next

end SszX86.IndicesChunkCount
