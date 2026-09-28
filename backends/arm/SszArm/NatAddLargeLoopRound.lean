import SszArm.NatAddLargeLoopMemory

namespace SszArm.NatAdd.LargeLoop

open SszNative
open NatCompare (Source Words Operand)
open Delimited (Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The physical loop invariant at PC1692. Original physical lists are kept
verbatim; only the allocated output suffix is writable. -/
structure Invariant (s : ArmState) (stack output : BitVec 64)
    (left right : List (BitVec 64)) (index remaining carry : Nat) : Prop where
  indexPositive : 1 ≤ index
  remainingPositive : 0 < remaining
  carryBound : carry ≤ 1
  stackPointer : r (.GPR 31#5) s = stack
  stackBound : 16 ≤ stack.toNat
  outputPointer : r (.GPR 9#5) s = output
  outputBound : output.toNat + 8 * (index + remaining) ≤ 2^64
  outputStack : Protected [(stack.toNat - 16, 16)] output.toNat (8 * (index + remaining))
  leftNonnull : r (.GPR 1#5) s ≠ 0#64
  leftCount : (r (.GPR 2#5) s).toNat = left.length
  leftSource : Source s (r (.GPR 1#5) s) left
  leftWords : Words s (r (.GPR 1#5) s) left
  leftOwned : Protected (suffixWrites stack output index remaining)
    (r (.GPR 1#5) s).toNat (8 * left.length)
  rightInput : Operand s (r (.GPR 3#5) s) (r (.GPR 4#5) s) right
  rightOwned : r (.GPR 3#5) s ≠ 0#64 →
    Protected (suffixWrites stack output index remaining)
      (r (.GPR 3#5) s).toNat (8 * right.length)
  rightSmall : r (.GPR 13#5) s = if r (.GPR 3#5) s = 0#64 then 1#64 else 0#64
  carryRegister : r (.GPR 12#5) s = BitVec.ofNat 64 carry
  remainingRegister : r (.GPR 14#5) s = BitVec.ofNat 64 remaining
  indexRegister : r (.GPR 15#5) s = BitVec.ofNat 64 index

/-- One whole actual iteration, including all left/right branches, both
ADDS instructions, the eight-instruction spill/store, and the real backedge. -/
theorem round_run (s : ArmState) (base stack output : BitVec 64)
    (left right : List (BitVec 64)) (index remaining carry : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1692#64)
    (inv : Invariant s stack output left right index remaining carry) :
    let next := LimbAdd.step (left[index]?.getD 0) (right[index]?.getD 0) carry
    ∃ fuel t, run fuel s = t ∧ LoopFrame (suffixWrites stack output index remaining) s t ∧
      read_pc t = base + (if remaining = 1 then 2044#64 else 1692#64) ∧
      r (.GPR 12#5) t = BitVec.ofNat 64 next.2 ∧
      r (.GPR 14#5) t = BitVec.ofNat 64 (remaining - 1) ∧
      r (.GPR 15#5) t = BitVec.ofNat 64 (index + 1) ∧
      r (.GPR 13#5) t = r (.GPR 13#5) s ∧
      read_mem_bytes 8 (output + BitVec.ofNat 64 (8 * index)) t = next.1 := by
  have bound := inv.outputBound
  have pos := inv.remainingPositive
  have indexBound : index < 2^64 := by omega
  have h15 : (r (.GPR 15#5) s).toNat = index := by
    rw [inv.indexRegister]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound]
  obtain ⟨preFuel, u, urun, uf, up, ul, ur, ureg⟩ := operands_run s base left right index
    (suffixWrites stack output index remaining) hc he ha hp inv.leftCount
    inv.indexPositive h15 inv.rightSmall inv.leftSource inv.leftWords inv.rightInput
    inv.rightOwned (by simp [suffixWrites, inv.stackPointer])
  have address : storeAddress u .large = output + BitVec.ofNat 64 (8 * index) := by
    simp only [storeAddress, StoreKind.index, ureg 9#5 (by decide) (by decide),
      ureg 15#5 (by decide) (by decide), inv.outputPointer, inv.indexRegister]
    congr 1
    bv_omega
  have addressNat : (storeAddress u .large).toNat = output.toNat + 8 * index := by
    rw [address]
    bv_omega
  have usp : r (.GPR 31#5) u = stack := uf.sp.trans inv.stackPointer
  have apart : Protected [((storeAddress u .large).toNat, 8)]
      (r (.GPR 31#5) u - 16#64).toNat 8 := by
    have head := inv.outputStack.subspan (8 * index) 8 (by omega)
    rcases head with empty | separate
    · omega
    · right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      have sep := separate (stack.toNat - 16, 16) (by simp)
      have hs := inv.stackBound
      rw [addressNat, usp]
      simp only [Prod.fst, Prod.snd] at *
      bv_omega
  obtain ⟨bodyFuel, t, trun, tf, tp, t12, t14, t15, t13, stored⟩ :=
    body_run u base (left[index]?.getD 0) (right[index]?.getD 0) index remaining carry
      (suffixWrites stack output index remaining) (uf.code hc) (uf.error.trans he)
      (uf.aligned ha) up (by omega) pos (by omega) inv.carryBound
      (by rw [ureg 12#5 (by decide) (by decide)]; exact inv.carryRegister)
      (by rw [ureg 14#5 (by decide) (by decide)]; exact inv.remainingRegister)
      (by rw [ureg 15#5 (by decide) (by decide)]; exact inv.indexRegister) ul ur
      (by rw [usp]; exact inv.stackBound) (by rw [addressNat]; omega) apart
      (by simp [suffixWrites, usp]) (by
        intro a low high
        refine ⟨(output.toNat + 8 * index, 8 * remaining), by simp [suffixWrites], ?_, ?_⟩
        · simpa only [addressNat] using low
        · rw [addressNat] at high; omega)
  refine ⟨preFuel + bodyFuel, t, ?_, uf.trans tf, tp, t12, t14, t15, ?_, ?_⟩
  · rw [run_plus, urun, trun]
  · exact t13.trans (ureg 13#5 (by decide) (by decide))
  · simpa only [address] using stored

/-- Preservation of the physical invariant after a nonfinal iteration. -/
theorem invariant_next {s t : ArmState} (stack output : BitVec 64)
    (left right : List (BitVec 64)) (index remaining carry : Nat)
    (inv : Invariant s stack output left right index (remaining + 1) carry)
    (nonfinal : 0 < remaining)
    (frame : LoopFrame (suffixWrites stack output index (remaining + 1)) s t)
    (h12 : r (.GPR 12#5) t = BitVec.ofNat 64
      (LimbAdd.step (left[index]?.getD 0) (right[index]?.getD 0) carry).2)
    (h14 : r (.GPR 14#5) t = BitVec.ofNat 64 remaining)
    (h15 : r (.GPR 15#5) t = BitVec.ofNat 64 (index + 1))
    (h13 : r (.GPR 13#5) t = r (.GPR 13#5) s) :
    Invariant t stack output left right (index + 1) remaining
      (LimbAdd.step (left[index]?.getD 0) (right[index]?.getD 0) carry).2 := by
  have r1 := frame.registers 1#5 (by decide)
  have r2 := frame.registers 2#5 (by decide)
  have r3 := frame.registers 3#5 (by decide)
  have r4 := frame.registers 4#5 (by decide)
  refine ⟨by omega, nonfinal, LimbAdd.step_carry_le _ _ _ inv.carryBound,
    frame.sp.trans inv.stackPointer, inv.stackBound,
    (frame.registers 9#5 (by decide)).trans inv.outputPointer, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, h12, h14, h15⟩
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using inv.outputBound
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using inv.outputStack
  · rw [r1]; exact inv.leftNonnull
  · rw [r2]; exact inv.leftCount
  · rw [r1]; exact frame.source _ _ inv.leftSource
  · rw [r1]; exact frame.words _ _ inv.leftSource inv.leftWords inv.leftOwned
  · rw [r1]; exact suffixProtected_next stack output index remaining _ _ inv.leftOwned
  · rw [r3, r4]; exact operand_frame frame _ _ _ inv.rightInput inv.rightOwned
  · rw [r3]
    intro nonnull
    exact suffixProtected_next stack output index remaining _ _ (inv.rightOwned nonnull)
  · rw [h13, r3]; exact inv.rightSmall

end SszArm.NatAdd.LargeLoop
