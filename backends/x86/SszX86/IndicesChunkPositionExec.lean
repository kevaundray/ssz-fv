import SszX86.IndicesChunkPositionImpl
import SszX86.DelimitedCore
import SszX86.NatCompareExec
import SszIndicesPaths

namespace SszX86.IndicesChunkPosition
open Kraken.X64.Parser
open SszNative UintCodec

macro "indices_position_step " chunk:ident " row " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member : ($chunk[$k]'(by decide)) ∈ SszX86.IndicesChunkPosition.program := by
     have selected : ($chunk[$k]'(by decide)) ∈ $chunk := List.getElem_mem (by decide)
     simp only [SszX86.IndicesChunkPosition.program, List.mem_append]
     simp only [selected, true_or, or_true]
   have fetched := SszX86.IndicesChunkPosition.step_at _ _ $hc
     ($chunk[$k]'(by decide)) member
   simp only [$chunk, List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.IndicesChunkPosition.directives, SszX86.IndicesChunkPosition.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bytesv, Width.bits]))

macro "indices_position_load " observation:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($observation), NatCompare.word_cast])

def bitShiftState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rbx := s.regs.rdi, rdi := s.regs.rsp,
    r9 := s.regs.rcx, rcx := 8, rsi := s.regs.r10, rdx := s.regs.r12, r8 := 0},
    status := flags}

/-- The bit-sequence caller passes the complete u128 shift (high word zero),
not merely a masked x86 shift count. -/
theorem bit_shift_setup_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (bitShiftState s flags, base + 970)) :
    Eventually (step e) P (s, base + 947) := by
  indices_position_step programChunk3 row 18 using code
  indices_position_step programChunk3 row 19 using code
  indices_position_step programChunk3 row 20 using code
  indices_position_step programChunk3 row 21 using code
  indices_position_step programChunk3 row 22 using code
  indices_position_step programChunk3 row 23 using code
  indices_position_step programChunk3 row 24 using code
  constructor <;> simpa only [bitShiftState] using next _

def packedShiftState (s : MachineData) (amount : Nat) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rcx := UInt64.ofNat amount, rdi := s.regs.rsp,
    rsi := s.regs.r10, rdx := s.regs.r12, r8 := 0}, status := flags}

private theorem packed_register (amount : Fin 6) :
    ((BitVec.ofNat 64 amount.val).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 amount.val := by
  have all : ∀ amount : Fin 6,
      ((BitVec.ofNat 64 amount.val).setWidth 32).setWidth 64 =
        BitVec.ofNat 64 amount.val := by decide
  exact all amount

/-- On the packing path the source-proved finite amount survives MOVL exactly.
Logical position metadata is not bounded by this internal shift contract. -/
theorem packed_shift_setup_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (amount : Fin 6) (stored : s.regs.rbp = UInt64.ofNat amount.val)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (packedShiftState s amount.val flags, base + 2087)) :
    Eventually (step e) P (s, base + 2073) := by
  indices_position_step programChunk7 row 4 using code
  simp only [stored, UInt64.toBitVec_ofNat', packed_register]
  indices_position_step programChunk7 row 5 using code
  indices_position_step programChunk7 row 6 using code
  indices_position_step programChunk7 row 7 using code
  indices_position_step programChunk7 row 8 using code
  constructor <;> simpa only [packedShiftState] using next _

theorem bit_shift_amount (s : MachineData) (flags : StatusFlags) :
    (bitShiftState s flags).regs.rcx.toNat +
      2^64 * (bitShiftState s flags).regs.r8.toNat ≤ 8 := by
  decide +kernel

theorem packed_shift_amount (s : MachineData) (amount : Fin 6) (flags : StatusFlags) :
    (packedShiftState s amount.val flags).regs.rcx.toNat +
      2^64 * (packedShiftState s amount.val flags).regs.r8.toNat ≤ 8 := by
  have bound := amount.isLt
  simp only [packedShiftState, UInt64.toNat_ofNat]
  omega

end SszX86.IndicesChunkPosition
