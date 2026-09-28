import SszX86.NatAddCarryExec

namespace SszX86.NatAdd.Carry.Entry
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def setupState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := 1
      r11 := UInt64.ofBitVec (-get s .rax)
      rbp := UInt64.ofBitVec ((get s .rbp).extractLsb' 8 56 ++ ((get s .rbp).setWidth 8 ^^^ 1#8))}
    status := flags}

theorem setup_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (setupState s flags, base + 1008)) :
    Eventually (step e) P (s, base + 935) := by
  natadd_step 244 using hc
  natadd_step 245 using hc
  natadd_step 246 using hc
  natadd_step 247 using hc
  constructor
  all_goals natadd_step 248 using hc
  all_goals simpa [setupState, get, Reg64s.get64] using hp _

end SszX86.NatAdd.Carry.Entry
