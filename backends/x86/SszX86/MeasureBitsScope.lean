import SszX86.MeasureBitsOutputMemory
import SszX86.MeasureBitsLoads

namespace SszX86.Measure.Bits
open UintCodec

def scopeFinal (s : MachineData) (pointer payload : BitVec 64) (flags : StatusFlags) : MachineData :=
  {scopePrepared s pointer payload flags with
    dmem := scopeMem s.dmem s.regs.rbx.toBitVec pointer payload
      s.regs.rcx.toBitVec s.regs.rax.toBitVec}

theorem scope_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64) (P : MachineState → Prop)
    (hm : OutputMapped s)
    (hp : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (pointer.toNat : Int))
    (hv : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (payload.toNat : Int))
    (next : ∀ flags, Eventually (step e) P (scopeFinal s pointer payload flags, base + 3335)) :
    Eventually (step e) P (s, base + 2893) := by
  apply scope_prepare_cps e base hc s pointer payload P hm hp hv
  intro flags
  apply scope_tail_cps e base hc
  · dsimp only [OutputMapped, scopePrepared]
    repeat' first | exact hm | apply Large.mapped_store
  · simpa only [scopeFinal, scopePrepared, scopeMem] using next flags

end SszX86.Measure.Bits
