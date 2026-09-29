import SszX86.IndicesNatShrImpl
import SszX86.IndicesNatShrCounterexampleMemory
import SszX86.DelimitedCore

namespace SszX86.IndicesNatShr.Counterexample

open Kraken.X64.Parser

/-- Concrete caller-saved registers; unspecified callee-saved registers are zero.
The flags stay quantified because TEST and shifts have undefined flag outputs. -/
def state (m : DataMem) (a c si eight nine ten eleven sp : UInt64)
    (flags : StatusFlags) : MachineData :=
  { regs := { rax := a, rcx := c, rdx := 2, rsi := si, rdi := 4096,
      r8 := eight, r9 := nine, r10 := ten, r11 := eleven, rsp := sp }
    status := flags, dmem := m }

def initial (m : DataMem) (flags : StatusFlags) : MachineData :=
  state m 0 64 8192 0 12288 0 0 16384 flags

def at39 (m : DataMem) (flags : StatusFlags) : MachineData :=
  state m 2 64 8192 0 12288 0 2 16384 flags

def at80 (m : DataMem) (flags : StatusFlags) : MachineData :=
  state m 64 64 8192 0 12288 0 2 16384 flags

def at109 (m : DataMem) (flags : StatusFlags) : MachineData :=
  state (scratchMem m) 64 64 8192 0 18446744073709551615 2 2 16368 flags

def at117 (m : DataMem) (flags : StatusFlags) : MachineData :=
  state (scratchMem m) 64 64 8192 0 1 0 2 16368 flags

def at150 (m : DataMem) (flags : StatusFlags) : MachineData :=
  state (scratchMem m) 64 64 8192 0 12288 0 66 16384 flags

def at169 (m : DataMem) (flags : StatusFlags) : MachineData := at150 m flags

def at192 (m : DataMem) (flags : StatusFlags) : MachineData :=
  state (scratchMem m) 18446744073709551615 64 8192 0 12288 0 2 16384 flags

def at665 (m : DataMem) (flags : StatusFlags) : MachineData :=
  state (scratchMem m) 5 64 8192 64 12288 0 2 16384 flags

def at680 (m : DataMem) (flags : StatusFlags) : MachineData :=
  state (scratchMem m) 5 192 7 64 12288 0 2 16384 flags

def at696 (m : DataMem) (flags : StatusFlags) : MachineData :=
  state (returnedMem m) 0 192 7 64 12288 0 2 16384 flags

def returned (m : DataMem) (flags : StatusFlags) : MachineData :=
  state (returnedMem m) 0 192 7 64 12288 0 2 16392 flags

macro "shr_counter_chunk_step " chunk:ident " row " k:num " using " hc:term : tactic => `(tactic|
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
      ShiftCountExpr.interpMasked, ShiftCountExpr.interp, StatusFlags.from_result,
      Int64.add_assoc, Width.bytes, Width.bits, state, -Bool.forall_bool]
   repeat' intro))

macro "shr_counter_load " h:term : tactic => `(tactic|
  simp (config := {instances := true}) [MachineData.load, Width.bytes, Width.bits,
    Effects.All, BitVec.ofInt_add, BitVec.ofInt_toInt, ($h), -Bool.forall_bool])

macro "shr_counter_step " k:num " using " hc:term : tactic => do
  let chunk := Lean.mkIdent
    (if k.getNat < 64 then ``SszX86.IndicesNatShr.programChunk0
     else if k.getNat < 128 then ``SszX86.IndicesNatShr.programChunk1
     else if k.getNat < 192 then ``SszX86.IndicesNatShr.programChunk2
     else ``SszX86.IndicesNatShr.programChunk3)
  let row := Lean.Syntax.mkNumLit (toString (k.getNat % 64))
  `(tactic| shr_counter_chunk_step $chunk row $row using $hc)

end SszX86.IndicesNatShr.Counterexample
