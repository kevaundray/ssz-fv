import SszX86.IndicesHelperIndicesImpl
import SszX86.IndicesHelperIndicesBounds
import SszX86.NatCompareProofs

set_option autoImplicit false

namespace SszX86.IndicesHelperIndices
open Kraken.X64.Parser
open SszNative UintCodec

private theorem chunk7_member (row : Nat × Nat × Program)
    (member : row ∈ programChunk7) : row ∈ program := by
  simp [program, member]

/-- Each reduction sees only one 64-row chunk and one current instruction. -/
macro "indices_helper_count_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.IndicesHelperIndices.step_at _ _ $hc
     (SszX86.IndicesHelperIndices.programChunk7[$k]'(by decide))
     (SszX86.IndicesHelperIndices.chunk7_member _ (List.getElem_mem (by decide)))
   simp only [SszX86.IndicesHelperIndices.programChunk7,
     List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.IndicesHelperIndices.directives, SszX86.IndicesHelperIndices.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "indices_helper_count_load " loaded:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($loaded),
      SszX86.NatCompare.word_cast])

/-- The restored count-pass registers at the checked-add gate. The input
memory, stack, vectors, and every other register remain those of `s`. -/
def countGateState (s : MachineData) (count arena output cursor : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rcx := UInt64.ofBitVec count
    rax := UInt64.ofBitVec arena
    rdi := UInt64.ofBitVec output
    r8 := UInt64.ofBitVec cursor}, status := flags}

/-- The actual checked-add overflow edge, offsets2041--2074. The three MOVs
between CMP and JE preserve its flags; overflow is tested before incrementing
or reserving any output slots. -/
theorem count_gate_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (count arena output cursor : BitVec 64)
    (countLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 64) 8 =
      some (count.toNat : Int))
    (arenaLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 120) 8 =
      some (arena.toNat : Int))
    (outputLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 40) 8 =
      some (output.toNat : Int))
    (cursorLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 160) 8 =
      some (cursor.toNat : Int))
    (P : MachineState → Prop)
    (overflow : count = 18446744073709551615#64 → ∀ flags,
      Eventually (step e) P (countGateState s count arena output cursor flags, base + 3695))
    (continue : count ≠ 18446744073709551615#64 → ∀ flags,
      Eventually (step e) P (countGateState s count arena output cursor flags, base + 2074)) :
    Eventually (step e) P (s, base + 2041) := by
  have target := code.targets ("indices_helper_indices_u3695", 3695) (by decide)
  indices_helper_count_step 41 using code
  indices_helper_count_load countLoad
  indices_helper_count_step 42 using code
  indices_helper_count_step 43 using code
  indices_helper_count_load arenaLoad
  indices_helper_count_step 44 using code
  indices_helper_count_load outputLoad
  indices_helper_count_step 45 using code
  indices_helper_count_load cursorLoad
  indices_helper_count_step 46 using code
  by_cases full : count = 18446744073709551615#64
  · simpa [StatusFlags.from_result, NatCompare.zf_sub, full, target,
      countGateState, Effects.All] using overflow full _
  · simpa [StatusFlags.from_result, NatCompare.zf_sub, full,
      countGateState, Effects.All] using continue full _

/-- Relating the actual all-ones comparison to the source's checked increment
requires only a physical usize count, never a bound on a logical Nat input. -/
theorem checked_count_not_full (count : Nat) (bounded : count < 2 ^ 64) :
    BitVec.ofNat 64 count ≠ 18446744073709551615#64 ↔ count + 1 < 2 ^ 64 := by
  constructor
  · intro different
    by_contra overflow
    have same : count = 18446744073709551615 := by omega
    exact different (by simp [same])
  · intro fits same
    have observed := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded] at observed
    omega

end SszX86.IndicesHelperIndices
