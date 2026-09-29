import SszX86.IndicesNatShrSteps
import SszX86.IndicesNatShrArithmetic

set_option autoImplicit false

namespace SszX86.IndicesNatShr

def rightShiftState (s : MachineData) (bits : Nat) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r14 := UInt64.ofBitVec (s.regs.r14.toBitVec >>> bits)},
    status := flags}

/-- The original loop's SHR64 at PC642. Exhaustion is over the finite internal
amount domain, never over the unrestricted source limb. -/
theorem right_shift_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (bits : Nat) (amount : bits ≤ 8)
    (count : s.regs.rcx.toBitVec = BitVec.ofNat 64 bits)
    (post : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) post (rightShiftState s bits flags, base + 645)) :
    Eventually (step e) post (s, base + 642) := by
  have alternatives : bits = 0 ∨ bits = 1 ∨ bits = 2 ∨ bits = 3 ∨ bits = 4 ∨
      bits = 5 ∨ bits = 6 ∨ bits = 7 ∨ bits = 8 := by omega
  rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    indices_shr_step 179 using code
    simp (config := {instances := true})
      [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take, count, Effects.All]
    repeat' apply And.intro
    repeat' intro
    simpa [rightShiftState, StatusFlags.from_result, Effects.All] using next _

def leftShiftState (s : MachineData) (bits : Nat) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r12 := UInt64.ofBitVec (s.regs.r12.toBitVec <<< (64 - bits))},
    status := flags}

/-- The original high-limb SHL64 uses the complementary count only on a nonzero
shift arm, excluding the hardware-mask/source-shift discrepancy at zero. -/
theorem left_shift_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (bits : Nat) (positive : 0 < bits) (amount : bits ≤ 8)
    (count : s.regs.rcx.toBitVec = BitVec.ofNat 64 (64 - bits))
    (post : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) post (leftShiftState s bits flags, base + 599)) :
    Eventually (step e) post (s, base + 596) := by
  have alternatives : bits = 1 ∨ bits = 2 ∨ bits = 3 ∨ bits = 4 ∨
      bits = 5 ∨ bits = 6 ∨ bits = 7 ∨ bits = 8 := by omega
  rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    indices_shr_step 165 using code
    simp (config := {instances := true})
      [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take, count, Effects.All]
    repeat' apply And.intro
    repeat' intro
    simpa [leftShiftState, StatusFlags.from_result, Effects.All] using next _

def joinedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r12 := UInt64.ofBitVec (s.regs.r12.toBitVec ||| s.regs.r14.toBitVec)},
    status := flags}

/-- The carry limb is joined by the original OR, without imposing a bound on
any logical Nat value or on the contents of either physical input limb. -/
theorem join_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (post : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) post (joinedState s flags, base + 602)) :
    Eventually (step e) post (s, base + 599) := by
  indices_shr_step 166 using code
  repeat' apply And.intro
  repeat' intro
  simpa [joinedState, StatusFlags.from_result, Effects.All] using next _

end SszX86.IndicesNatShr
