import SszArm.NatAddSmallLoopRound

namespace SszArm.NatAdd.SmallLoop

open UintCodec SszNative
open NatCompare (Source Words)
open Delimited (Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The invariant at +1980 describes the next unread physical index and the
remaining allocated words. At zero remaining it instead describes +2044. -/
structure Invariant (s : ArmState) (base : BitVec 64) (index remaining carryValue : Nat) : Prop where
  pc : read_pc s = base + (if remaining = 0 then 2044#64 else 1980#64)
  carry : r (.GPR 12#5) s = BitVec.ofNat 64 carryValue
  remaining : r (.GPR 13#5) s = BitVec.ofNat 64 remaining
  index : r (.GPR 14#5) s = BitVec.ofNat 64 index
  carryBound : carryValue ≤ 1

/-- Entire arbitrary-length Small-left/Large-right carry suffix. Physical input
length is not replaced by significant length: high zero limbs remain readable,
and the allocation's extra carry word is always written. There is no execution
premise: the fuel and final state are constructed from the actual instruction
round, including both lowering spills. -/
theorem loop_run (remaining : Nat) (base pointer sp output : BitVec 64)
    (right : List (BitVec 64)) (allocated : Nat) :
    ∀ (s : ArmState) (index carry : Nat),
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    r (.GPR 3#5) s = pointer →
    r (.GPR 4#5) s = BitVec.ofNat 64 right.length →
    r (.GPR 9#5) s = output → r (.GPR 31#5) s = sp →
    Layout sp output allocated → index + remaining ≤ allocated →
    Invariant s base index remaining carry →
    Source s pointer right → Words s pointer right →
    Protected (writes sp output index remaining) pointer.toNat (8 * right.length) →
    ∃ fuel t, run fuel s = t ∧
      LoopFrame (writes sp output index remaining) s t ∧
      Invariant t base (index + remaining) 0
        (LimbAdd.loop remaining [] (right.drop index) carry).2 ∧
      (∀ j, j < remaining → read_mem_bytes 8 (address output (index + j)) t =
        (LimbAdd.loop remaining [] (right.drop index) carry).1[j]?.getD 0#64) := by
  induction remaining with
  | zero =>
    intro s index carry hc he ha h3 h4 h9 hsp layout fit inv source words owned
    refine ⟨0, s, rfl, LoopFrame.refl _ s, ?_, ?_⟩
    · simpa only [Nat.add_zero, LimbAdd.loop] using inv
    · intro j hj
      omega
  | succ remaining ih =>
    intro s index carry hc he ha h3 h4 h9 hsp layout fit inv source words owned
    have hp : read_pc s = base + 1980#64 := by simpa using inv.pc
    obtain ⟨runRound, roundFrame, nextCarry, nextRemaining, nextIndex, nextPC, nextWord⟩ :=
      round_run s base pointer sp output right allocated index remaining carry
        hc he ha hp h3 h4 h9 inv.carry inv.remaining inv.index hsp layout fit
        inv.carryBound source words
    let v := roundState s base right index
    let next := LimbAdd.step 0#64 (right[index]?.getD 0#64) carry
    change run (roundFuel s base right index) s = v at runRound
    change LoopFrame (writes sp output index (remaining + 1)) s v at roundFrame
    change r (.GPR 12#5) v = BitVec.ofNat 64 next.2 at nextCarry
    change r (.GPR 13#5) v = BitVec.ofNat 64 remaining at nextRemaining
    change r (.GPR 14#5) v = BitVec.ofNat 64 (index + 1) at nextIndex
    change read_pc v = base + (if remaining = 0 then 2044#64 else 1980#64) at nextPC
    change read_mem_bytes 8 (address output index) v = next.1 at nextWord
    have nextInv : Invariant v base (index + 1) remaining next.2 :=
      ⟨nextPC, nextCarry, nextRemaining, nextIndex,
        LimbAdd.step_carry_le _ _ _ inv.carryBound⟩
    have nextOwned : Protected (writes sp output (index + 1) remaining)
        pointer.toNat (8 * right.length) := narrow_owned (by omega) (by omega) owned
    obtain ⟨fuel, t, runRest, restFrame, finalInv, finalWords⟩ :=
      ih v (index + 1) next.2 (roundFrame.code hc) (roundFrame.error.trans he)
        (roundFrame.aligned ha) ((roundFrame.registers _ (by decide)).trans h3)
        ((roundFrame.registers _ (by decide)).trans h4)
        ((roundFrame.registers _ (by decide)).trans h9) (roundFrame.sp.trans hsp)
        layout (by omega) nextInv (roundFrame.source _ _ source)
        (roundFrame.words _ _ source words owned) nextOwned
    have recur := suffix_succ remaining index carry right
    change LimbAdd.loop (remaining + 1) [] (right.drop index) carry =
      (next.1 :: (LimbAdd.loop remaining [] (right.drop (index + 1)) next.2).1,
        (LimbAdd.loop remaining [] (right.drop (index + 1)) next.2).2) at recur
    refine ⟨roundFuel s base right index + fuel, t, ?_,
      roundFrame.trans (widen_frame sp output index (remaining + 1)
        (index + 1) remaining (by omega) (by omega) restFrame), ?_, ?_⟩
    · rw [run_plus, runRound, runRest]
    · simpa only [recur, Nat.add_assoc, Nat.add_comm 1 remaining] using finalInv
    · intro j hj
      cases j with
      | zero =>
        have addressNat := address_nat layout (show index < allocated by omega)
        have physical : (address output index).toNat + 8 ≤ 2^64 := by
          rw [addressNat]
          have := layout.physical
          omega
        have protectedWord : Protected (writes sp output (index + 1) remaining)
            (address output index).toNat 8 := by
          right
          intro span member
          simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · rw [addressNat]
            have := layout.separate
            have := layout.stack
            omega
          · rw [addressNat]
            left
            omega
        have preserved := restFrame.memory.read (address output index) 8 physical protectedWord
        simpa only [Nat.add_zero, recur, List.getElem?_cons_zero, Option.getD_some] using
          preserved.trans nextWord
      | succ j =>
        have readNext := finalWords j (by omega)
        simpa only [recur, List.getElem?_cons_succ, Nat.add_assoc,
          Nat.add_comm 1 j] using readNext

/-- Input byte preservation follows from the very same physical frame used to
protect every already-written output word; aliases among immutable inputs are
not forbidden. -/
theorem input_bytes {s t : ArmState} {sp output pointer : BitVec 64}
    {index remaining : Nat} {right : List (BitVec 64)}
    (frame : LoopFrame (writes sp output index remaining) s t)
    (owned : Protected (writes sp output index remaining) pointer.toNat (8 * right.length)) :
    ∀ a : BitVec 64, pointer.toNat ≤ a.toNat →
      a.toNat < pointer.toNat + 8 * right.length → t.mem a = s.mem a := by
  intro a low high
  exact frame.memory.protected_byte owned a low high

end SszArm.NatAdd.SmallLoop
