import SszX86.NatAddSmallSum
import SszX86.NatAddSmallMath
import SszX86.NatAddControl

namespace SszX86.NatAdd
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

structure SumReady (s t : MachineData) (left right : NatOperand) : Prop where
  frame : ControlFrame s t
  low : t.regs.rdx.toBitVec = (SszNative.NatAdd.sumWide left right).setWidth 64
  high : t.regs.rax.toBitVec = ((SszNative.NatAdd.sumWide left right) >>> 64).setWidth 64

def sumTarget (left right : NatOperand) (base : Int64) : Int64 :=
  if (SszNative.NatAdd.sumWide left right).toNat < 2^64 then base + 250 else base + 676

private theorem sum_start_eq (s : MachineData) (zero : s.regs.rax = 0) : sumStart s = s := by
  cases s with
  | mk regs zmms flags dmem =>
    cases regs
    simp_all [sumStart]

/-- Every duplicated ADD/ADC site refines the exact shared widened sum. -/
theorem sum_sites_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand) (zero : s.regs.rax = 0)
    (hl : s.regs.rdx.toBitVec = SszNative.NatAdd.lowWord left)
    (hr : s.regs.r8.toBitVec = SszNative.NatAdd.lowWord right)
    (P : MachineState → Prop)
    (next : ∀ t, SumReady s t left right → Eventually (step e) P (t, sumTarget left right base)) :
    Eventually (step e) P (s, base + 237) ∧
      Eventually (step e) P (s, base + 647) ∧
      Eventually (step e) P (s, base + 663) ∧
      Eventually (step e) P (s, base + 844) := by
  have leftNat := congrArg BitVec.toNat hl
  have rightNat := congrArg BitVec.toNat hr
  change s.regs.rdx.toNat = (SszNative.NatAdd.lowWord left).toNat at leftNat
  change s.regs.r8.toNat = (SszNative.NatAdd.lowWord right).toNat at rightNat
  have target : sumExit s base = sumTarget left right base := by
    simp only [sumExit, sumTarget, SszNative.NatAdd.sumWide,
      LimbAdd.wideSum_toNat _ _ 0 (by omega), Nat.add_zero]
    rw [← leftNat, ← rightNat]
  have continuation (flags : StatusFlags) : Eventually (step e) P (sumState s flags, sumExit s base) := by
    rw [target]
    apply next
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
    · simpa only [sumState, UInt64.toBitVec_ofBitVec, SszNative.NatAdd.sumWide,
        hl, hr] using (wide_low (SszNative.NatAdd.lowWord left) (SszNative.NatAdd.lowWord right)).symm
    · simpa only [sumState, UInt64.toBitVec_ofBitVec, SszNative.NatAdd.sumWide,
        leftNat, rightNat] using (wide_high (SszNative.NatAdd.lowWord left) (SszNative.NatAdd.lowWord right)).symm
  rw [← sum_start_eq s zero]
  exact ⟨small_sum_cps e base hc s P continuation,
    loaded_sum_cps e base hc s P continuation,
    inline_sum_cps e base hc s P continuation,
    empty_sum_cps e base hc s P continuation⟩

end SszX86.NatAdd
