import SszX86.NatDivisionCore

namespace SszX86.NatDivision
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def smallState (s : MachineData) (lo hi : BitVec 64) (flags : StatusFlags) : MachineData :=
  { s with
    regs := { s.regs with r15 := UInt64.ofBitVec lo, rsi := UInt64.ofBitVec hi }
    status := flags }

def arguments (s : MachineData) (flags : StatusFlags) : MachineData :=
  { s with
    regs := { s.regs with
      r14 := 0, rdi := s.regs.r15, rdx := s.regs.r13, rcx := 0 }
    status := flags }

/-- The private Rust ABI moves the two numerator words into SysV divider
arguments; no C hidden-sret register is involved. -/
theorem arguments_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (arguments s flags, base + 261)) :
    Eventually (step e) P (s, base + 250) := by
  natdiv_step 65 using hc
  constructor <;> natdiv_step 66 using hc
  all_goals natdiv_step 67 using hc
  all_goals natdiv_step 68 using hc
  all_goals constructor <;> simpa [arguments] using hp _

/-- Immediate operands enter the same real wide-divider call as borrowed
one- and two-limb operands. -/
theorem immediate_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (smallState s s.regs.rdx.toBitVec 0 flags, base + 250)) :
    Eventually (step e) P (s, base + 214) := by
  natdiv_step 51 using hc
  constructor <;> natdiv_step 52 using hc
  all_goals natdiv_step 53 using hc
  all_goals simpa [smallState] using hp _

/-- Empty borrowed input reaches the genuine zero-numerator dispatch. -/
theorem empty_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (smallState s 0 0 flags, base + 250)) :
    Eventually (step e) P (s, base + 245) := by
  natdiv_step 63 using hc
  constructor <;> natdiv_step 64 using hc
  all_goals constructor <;> simpa [smallState] using hp _

/-- Loading the first two original limbs does not require a canonical stored
length. Any redundant high zeros have already been inspected by the scan. -/
theorem borrowed_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (lo hi : BitVec 64)
    (hlo : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (lo.toNat : Int))
    (hhi : 2 ≤ s.regs.rdx.toBitVec.toNat →
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (hi.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (smallState s lo (if s.regs.rdx.toBitVec.toNat < 2 then 0 else hi) flags, base + 250)) :
    Eventually (step e) P (s, base + 226) := by
  have target := hc.targets ("natDivision_u241", 241) (by decide)
  natdiv_step 56 using hc
  natdiv_load hlo
  natdiv_step 57 using hc
  natdiv_step 58 using hc
  by_cases short : s.regs.rdx.toBitVec.toNat < 2
  · have branch : s.regs.rdx.toNat < 2 := short
    simp only [branch, target]
    natdiv_step 61 using hc
    constructor <;> natdiv_step 62 using hc
    all_goals simpa [smallState, branch] using hp _
  · have branch : ¬ s.regs.rdx.toNat < 2 := short
    simp only [branch]
    natdiv_step 59 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
    natdiv_load (hhi (by omega))
    natdiv_step 60 using hc
    simpa [smallState, branch] using hp _

end SszX86.NatDivision
