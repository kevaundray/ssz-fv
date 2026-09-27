import SszX86.NatAddCarryExec

namespace SszX86.NatAdd.Carry.Pair.Cuts
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def startState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rdx := s.regs.rsi}
    status := flags}

def firstLoadState (s : MachineData) (value : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r15 := UInt64.ofBitVec value}
    status := flags}

def secondGuardState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r15 := UInt64.ofBitVec (get s .rdx + 1#64)}
    status := flags}

def secondLoadState (s : MachineData) (value : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r12 := UInt64.ofBitVec value}
    status := flags}

theorem start_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (startState s flags,
      if (get s .rsi).toNat < (get s .r8).toNat then base + 1260 else base + 1266)) :
    Eventually (step e) P (s, base + 1252) := by
  have target := hc.targets ("natAdd_u1266", 1266) (by decide)
  natadd_step 328 using hc
  natadd_step 329 using hc
  natadd_step 330 using hc
  by_cases present : s.regs.rsi.toNat < s.regs.r8.toNat
  all_goals simpa [startState, get, Reg64s.get64, StatusFlags.from_result, present, target, Effects.All] using hp _

theorem load_first_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64)
    (hl : Mem.loadInt s.dmem (get s .rcx + get s .rdx * 8#64) 8 = some (value.toNat : Int))
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (firstLoadState s value s.status, base + 1269)) :
    Eventually (step e) P (s, base + 1260) := by
  simp only [get, Reg64s.get64] at hl
  natadd_step 331 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natadd_load hl
  natadd_step 332 using hc
  simpa only [firstLoadState, get, Reg64s.get64] using hp

theorem zero_first_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (firstLoadState s 0 flags, base + 1269)) :
    Eventually (step e) P (s, base + 1266) := by
  natadd_step 333 using hc
  constructor <;> simpa [firstLoadState] using hp _

theorem second_guard_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (secondGuardState s flags,
      if (get s .rdx + 1#64).toNat < (get s .r8).toNat then base + 1221 else base + 1292)) :
    Eventually (step e) P (s, base + 1283) := by
  have target := hc.targets ("natAdd_u1221", 1221) (by decide)
  have incrementNat :
      ((s.regs.rdx.toBitVec.toInt + 1) % 18446744073709551616).toNat =
        (s.regs.rdx.toBitVec + 1#64).toNat := by
    have modulus : (18446744073709551616 : Int) = ((2^64 : Nat) : Int) := by decide
    have cast : BitVec.ofInt 64 (s.regs.rdx.toBitVec.toInt + 1) =
        s.regs.rdx.toBitVec + 1#64 := by
      rw [BitVec.ofInt_add, BitVec.ofInt_toInt]
      rfl
    simpa only [BitVec.toNat_ofInt, modulus] using congrArg BitVec.toNat cast
  natadd_step 338 using hc
  natadd_step 339 using hc
  natadd_step 340 using hc
  by_cases present : (s.regs.rdx.toNat + 1) % 18446744073709551616 < s.regs.r8.toNat
  all_goals simpa [secondGuardState, get, Reg64s.get64, StatusFlags.from_result, target,
    incrementNat, BitVec.ofInt_add, BitVec.ofInt_toInt, present, Effects.All] using hp _

theorem load_second_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64)
    (hl : Mem.loadInt s.dmem (get s .rcx + get s .rdx * 8#64 + 8#64) 8 = some (value.toNat : Int))
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (secondLoadState s value s.status, base + 1226)) :
    Eventually (step e) P (s, base + 1221) := by
  simp only [get, Reg64s.get64] at hl
  natadd_step 319 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natadd_load hl
  simpa only [secondLoadState, get, Reg64s.get64] using hp

theorem zero_second_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (secondLoadState s 0 flags, base + 1226)) :
    Eventually (step e) P (s, base + 1292) := by
  natadd_step 341 using hc
  constructor
  all_goals natadd_step 342 using hc
  all_goals simpa [secondLoadState] using hp _

end SszX86.NatAdd.Carry.Pair.Cuts
