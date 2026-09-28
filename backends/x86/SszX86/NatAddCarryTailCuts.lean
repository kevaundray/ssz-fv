import SszX86.NatAddCarryExec

namespace SszX86.NatAdd.Carry.Pair.Tail
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def indexState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rdx := UInt64.ofBitVec (get s .rdx + 2#64)}
    status := flags}

def wordState (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rcx := UInt64.ofBitVec limb}
    status := flags}

def sumState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rcx := UInt64.ofBitVec (get s .rcx + get s .r14)}
    status := flags}

def address (s : MachineData) : BitVec 64 := get s .r10 + get s .rdx * 8#64

def storedState (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem (address s) 8 (get s .rcx).toInt}

theorem parity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P ({s with status := flags},
      if (get s .rax).extractLsb' 0 8 &&& 1#8 = 0#8 then base + 1325 else base + 1301)) :
    Eventually (step e) P (s, base + 1297) := by
  have target := hc.targets ("natAdd_u1325", 1325) (by decide)
  natadd_step 343 using hc
  constructor
  all_goals natadd_step 344 using hc
  all_goals by_cases even : 1#8 &&& s.regs.rax.toBitVec.setWidth 8 = 0#8
  all_goals simpa [get, Reg64s.get64, StatusFlags.from_result, even, target,
    Effects.All, BitVec.and_comm] using hp _

theorem index_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (indexState s flags,
      if (get s .rdx + 2#64).toNat < (get s .r8).toNat then base + 1310 else base + 1316)) :
    Eventually (step e) P (s, base + 1301) := by
  have target := hc.targets ("natAdd_u1316", 1316) (by decide)
  natadd_step 345 using hc
  natadd_step 346 using hc
  natadd_step 347 using hc
  by_cases present : (s.regs.rdx.toNat + 2) % 18446744073709551616 < s.regs.r8.toNat
  all_goals simp only [Nat.add_comm] at present
  all_goals simpa [indexState, get, Reg64s.get64, StatusFlags.from_result, present,
    target, Effects.All, BitVec.add_comm, UInt64.add_comm, Nat.add_comm] using hp _

theorem word_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (hl : Mem.loadInt s.dmem (get s .rcx + get s .rdx * 8#64) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (wordState s limb s.status, base + 1318)) :
    Eventually (step e) P (s, base + 1310) := by
  simp only [get, Reg64s.get64] at hl
  natadd_step 348 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natadd_load hl
  natadd_step 349 using hc
  simpa only [wordState] using hp

theorem zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (wordState s 0 flags, base + 1318)) :
    Eventually (step e) P (s, base + 1316) := by
  natadd_step 350 using hc
  constructor <;> simpa [wordState] using hp _

theorem sum_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (sumState s flags, base + 1321)) :
    Eventually (step e) P (s, base + 1318) := by
  natadd_step 351 using hc
  simpa [sumState, get, Reg64s.get64, UInt64.add_comm] using hp _

theorem store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : ∃ old, Mem.loadInt s.dmem (address s) 8 = some old)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (storedState s, base + 1325)) :
    Eventually (step e) P (s, base + 1321) := by
  natadd_step 352 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · exact hm
  simpa [storedState, address, get, Reg64s.get64, Effects.All] using hp

end SszX86.NatAdd.Carry.Pair.Tail
