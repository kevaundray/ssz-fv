import SszX86.NatAddCarryEntryArithmetic

namespace SszX86.NatAdd.Carry.Entry
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def storedState (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (get s .r10) 8 (get s .r9).toInt}

def sumStoredState (s : MachineData) (right : BitVec 64) (flags : StatusFlags) : MachineData :=
  {addedState s right flags with
    dmem := Mem.storeInt s.dmem (get s .r10) 8 (right + get s .r9).toInt}

def smallMarkedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rbp := 0}
    status := flags}

def largeMarkedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rbp := UInt64.ofBitVec ((get s .rbp).extractLsb' 8 56 ++ 1#8)}
    status := flags}

theorem small_store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : ∃ old, Mem.loadInt s.dmem (get s .r10) 8 = some old)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (storedState s, base + 910)) :
    Eventually (step e) P (s, base + 907) := by
  natadd_step 234 using hc
  try simp only [BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · exact hm
  simpa [storedState, get, Reg64s.get64, Effects.All] using hp

theorem large_store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : ∃ old, Mem.loadInt s.dmem (get s .r10) 8 = some old)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (storedState s, base + 927)) :
    Eventually (step e) P (s, base + 924) := by
  natadd_step 240 using hc
  try simp only [BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · exact hm
  simpa [storedState, get, Reg64s.get64, Effects.All] using hp

theorem large_sum_store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (zero : s.regs.r14 = 0)
    (hm : ∃ old, Mem.loadInt s.dmem (get s .r10) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (sumStoredState s (get s .r15) flags, base + 927)) :
    Eventually (step e) P (s, base + 917) := by
  apply large_add_cps e base hc s zero P
  intro flags
  apply large_store_cps e base hc (addedState s (get s .r15) flags)
  · exact hm
  exact hp flags

theorem small_mark_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (smallMarkedState s flags, base + 935)) :
    Eventually (step e) P (s, base + 910) := by
  natadd_step 235 using hc
  constructor
  all_goals natadd_step 236 using hc
  all_goals simpa [smallMarkedState] using hp _

theorem large_mark_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (largeMarkedState s flags,
      if get s .rsi = 0 then base + 1060 else base + 935)) :
    Eventually (step e) P (s, base + 927) := by
  have target := hc.targets ("natAdd_u1060", 1060) (by decide)
  natadd_step 241 using hc
  natadd_step 242 using hc
  constructor
  all_goals natadd_step 243 using hc
  all_goals by_cases zero : s.regs.rsi.toBitVec = 0#64
  all_goals simpa [largeMarkedState, get, Reg64s.get64, StatusFlags.from_result,
    zero, target, Effects.All] using hp _

end SszX86.NatAdd.Carry.Entry
