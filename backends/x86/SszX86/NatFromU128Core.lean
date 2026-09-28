import SszX86.NatFromU128Impl
import SszX86.DelimitedReservation
import SszX86.NatAddOutputMemory
import SszX86.NatToU128Memory

namespace SszX86.NatFromU128
open Kraken.X64.Parser
open SszNative UintCodec

macro "natfrom_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.NatFromU128.step_at _ _ $hc
     (SszX86.NatFromU128.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.NatFromU128.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.NatFromU128.program, SszX86.NatFromU128.directives,
      SszX86.NatFromU128.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "natfrom_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast])

structure ReadFrame (s t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  vectors : t.zmms = s.zmms
  registers : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
    t.regs.get64 r = s.regs.get64 r

def initial (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := 0}, status := flags}

theorem entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rdx.toBitVec = 0 → ∀ flags,
      Eventually (step e) P (initial s flags, base + 7))
    (wide : s.regs.rdx.toBitVec ≠ 0 → ∀ flags,
      Eventually (step e) P (initial s flags, base + 20)) :
    Eventually (step e) P (s, base) := by
  have target := hc.targets ("natFromU128_u20", 20) (by decide)
  rw [← Int64.add_zero base]
  natfrom_step 0 using hc
  constructor <;> natfrom_step 1 using hc
  all_goals constructor <;> natfrom_step 2 using hc
  all_goals
    by_cases zero : s.regs.rdx.toBitVec = 0#64
    · simpa [initial, StatusFlags.from_result, zero, Effects.All] using small zero _
    · simpa [initial, StatusFlags.from_result, zero, target, Effects.All] using wide zero _

end SszX86.NatFromU128
