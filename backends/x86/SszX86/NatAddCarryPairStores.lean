import SszX86.NatAddCarryExec

namespace SszX86.NatAdd.Carry.Pair.Cuts
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def firstStoreAddress (s : MachineData) : BitVec 64 :=
  get s .rbx + get s .rdx * 8#64 - 8#64

def firstStoreState (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (firstStoreAddress s) 8 (get s .r14).toInt}

def secondStoreAddress (s : MachineData) : BitVec 64 :=
  get s .rbx + get s .rdx * 8#64

def secondStoreState (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (secondStoreAddress s) 8 (get s .rsi).toInt}

theorem first_store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem (firstStoreAddress s) 8 = some old)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (firstStoreState s, base + 1283)) :
    Eventually (step e) P (s, base + 1278) := by
  natadd_step 337 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · simpa [firstStoreAddress, get, Reg64s.get64, BitVec.sub_eq_add_neg] using hm
  simpa [firstStoreState, firstStoreAddress, get, Reg64s.get64,
    Effects.All, BitVec.sub_eq_add_neg] using hp

theorem second_store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem (secondStoreAddress s) 8 = some old)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (secondStoreState s, base + 1243)) :
    Eventually (step e) P (s, base + 1239) := by
  natadd_step 324 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · exact hm
  simpa [secondStoreState, secondStoreAddress, get, Reg64s.get64, Effects.All] using hp

end SszX86.NatAdd.Carry.Pair.Cuts
