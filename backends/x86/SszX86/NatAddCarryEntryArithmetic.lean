import SszX86.NatAddCarryExec

namespace SszX86.NatAdd.Carry.Entry
open Kraken.X64.Parser
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def addedState (s : MachineData) (right : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r9 := UInt64.ofBitVec (right + get s .r9)
      r14 := UInt64.ofBitVec (BitVec.ofNat 64 (Udivti3.addFlags right (get s .r9)).cf.toNat)}
    status := flags}

theorem initial_add (left right : BitVec 64) :
    right + left = (LimbAdd.step left right 0).1 ∧
    BitVec.ofNat 64 (Udivti3.addFlags right left).cf.toNat =
      BitVec.ofNat 64 (LimbAdd.step left right 0).2 := by
  have leftBound := left.isLt
  have rightBound := right.isLt
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, LimbAdd.step, BitVec.toNat_ofNat, Nat.add_zero]
    rw [Nat.add_comm]
  · rw [Udivti3.addFlags_cf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, LimbAdd.step, Nat.add_zero, Udivti3.radix]
    by_cases overflow : 2^64 ≤ right.toNat + left.toNat
    all_goals simp only [overflow, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false]
    all_goals omega

theorem small_add_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (zero : s.regs.r14 = 0) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (addedState s (get s .r8) flags, base + 907)) :
    Eventually (step e) P (s, base + 900) := by
  natadd_step 232 using hc
  natadd_step 233 using hc
  simpa (config := {instances := true}) [addedState, get, Reg64s.get64, zero,
    Udivti3.addFlags_cf, StatusFlags.from_result, carry_byte] using hp _

theorem large_add_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (zero : s.regs.r14 = 0) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (addedState s (get s .r15) flags, base + 924)) :
    Eventually (step e) P (s, base + 917) := by
  natadd_step 238 using hc
  natadd_step 239 using hc
  simpa (config := {instances := true}) [addedState, get, Reg64s.get64, zero,
    Udivti3.addFlags_cf, StatusFlags.from_result] using hp _

end SszX86.NatAdd.Carry.Entry
