import SszArm.Udivti3Exec

namespace SszArm.Udivti3

open BitVec
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def wordLoopTrace : Nat → ArmState → List Nat
  | 0, _ => []
  | k+1, s => wordTrace s ++ wordLoopTrace k (wordRound s)

def wideLoopTrace : Nat → ArmState → List Nat
  | 0, _ => []
  | k+1, s => wideTrace s ++ wideLoopTrace k (wideRound s)

private theorem step_q_bound (d bit q r k : Nat) (hk : k < 64)
    (hq : q < 2^(64-(k+1))) :
    (Division.step d bit q r).1 < 2^(64-k) := by
  have h0 := prefix_bound_step 64 k q 0 hk hq (by decide)
  have h1 := prefix_bound_step 64 k q 1 hk hq (by decide)
  unfold Division.step
  dsimp only
  split <;> assumption

private theorem body_q_bound (k q : Nat) (hk : k < 64)
    (hq : q < 2^(64-(k+1))) : 2*q+1 < radix := by
  exact prefix_bound_radix k _ (by omega)
    (prefix_bound_step 64 k q 1 hk hq (by decide))

/-- A complete word pass. Its invariant permits an arbitrary initial quotient,
remainder and number of bits remaining; the counter decreases through zero. -/
theorem word_loop (k : Nat) (s : ArmState) (base : BitVec 64) (n : BitVec 64)
    (hk : k ≤ 64) (hn : (r (.GPR 7) s).toNat = k)
    (hp : read_pc s = if k = 0 then base+128#64 else base+88#64)
    (hs : r (.GPR 5) s = pending n k)
    (hq : (r (.GPR 0) s).toNat < 2^(64-k))
    (hr : (r (.GPR 6) s).toNat < (r (.GPR 2) s).toNat) :
    let t := block (wordLoopTrace k s) s
    Follows base (wordLoopTrace k s) s ∧ read_pc t = base+128#64 ∧
    (r (.GPR 7) t).toNat = 0 ∧
    (r (.GPR 0) t).toNat =
      (Division.loop (r (.GPR 2) s).toNat n.toNat k
        (r (.GPR 0) s).toNat (r (.GPR 6) s).toNat).1 ∧
    (r (.GPR 6) t).toNat =
      (Division.loop (r (.GPR 2) s).toNat n.toNat k
        (r (.GPR 0) s).toNat (r (.GPR 6) s).toNat).2 ∧
    r (.GPR 1) t = r (.GPR 1) s ∧
    r (.GPR 4) t = r (.GPR 4) s ∧ r (.GPR 8) t = r (.GPR 8) s := by
  induction k generalizing s with
  | zero => simpa [wordLoopTrace, block, Follows, Division.loop] using
      (show True ∧ read_pc s = base+128#64 ∧ (r (.GPR 7) s).toNat = 0 ∧
        (r (.GPR 0) s).toNat = (r (.GPR 0) s).toNat ∧
        (r (.GPR 6) s).toNat = (r (.GPR 6) s).toNat ∧
        r (.GPR 1) s = r (.GPR 1) s ∧ r (.GPR 4) s = r (.GPR 4) s ∧
        r (.GPR 8) s = r (.GPR 8) s from
        ⟨trivial, by simpa using hp, hn, rfl, rfl, rfl, rfl, rfl⟩)
  | succ k ih =>
    have hkl : k < 64 := by omega
    have hbit : topBit (r (.GPR 5) s) = (n.toNat / 2^k) % 2 := by
      rw [hs, pending_bit n k hkl]
    obtain ⟨hf, hpc, hcount, hquot, hrem, hstream, h1, h4, h8⟩ :=
      word_round s base (by simpa using hp) (by omega) (body_q_bound k _ hkl hq) hr
    have hd : r (.GPR 2) (wordRound s) = r (.GPR 2) s :=
      block_frame (wordTrace s) s (.GPR 2) (by decide)
    have hn' : (r (.GPR 7) (wordRound s)).toNat = k := by omega
    have hp' : read_pc (wordRound s) =
        if k = 0 then base+128#64 else base+88#64 := by
      rw [hpc, hn]
      by_cases hz : k = 0 <;> simp [hz]
    have hs' : r (.GPR 5) (wordRound s) = pending n k := by
      rw [hstream, hs, pending_next n k hkl]
    have hq' : (r (.GPR 0) (wordRound s)).toNat < 2^(64-k) := by
      rw [hquot]
      exact step_q_bound _ _ _ _ k hkl hq
    have hr' : (r (.GPR 6) (wordRound s)).toNat <
        (r (.GPR 2) (wordRound s)).toNat := by
      rw [hrem, hd]
      exact Division.step_remainder_lt _ _ _ _ hr (by omega) (topBit_lt _)
    obtain ⟨hfollow, hfinalpc, hzero, hfinalq, hfinalr, hfinal1, hfinal4, hfinal8⟩ :=
      ih (wordRound s) (by omega) hn' hp' hs' hq' hr'
    dsimp only
    rw [wordLoopTrace, block_append]
    rw [show block (wordTrace s) s = wordRound s from rfl]
    change Follows base (wordTrace s ++ wordLoopTrace k (wordRound s)) s ∧ _
    refine ⟨(follows_append _ _ _ _).2 ⟨hf, hfollow⟩,
      hfinalpc, hzero, ?_, ?_, hfinal1.trans h1, hfinal4.trans h4, hfinal8.trans h8⟩
    · rw [hfinalq, hd, hquot, hrem, hbit]
      rfl
    · rw [hfinalr, hd, hquot, hrem, hbit]
      rfl

/-- The wide pass additionally tracks the consumed-input prefix bound. This
proves the tentative remainder cannot overflow 128 bits, rather than assuming it. -/
theorem wide_loop (k : Nat) (s : ArmState) (base : BitVec 64) (n : BitVec 64)
    (hk : k ≤ 64) (hn : (r (.GPR 7) s).toNat = k)
    (hp : read_pc s = if k = 0 then base+236#64 else base+180#64)
    (hs : r (.GPR 4) s = pending n k)
    (hq : (r (.GPR 0) s).toNat < 2^(64-k))
    (hr : join (r (.GPR 5) s) (r (.GPR 6) s) < divisor s)
    (hb : join (r (.GPR 5) s) (r (.GPR 6) s) < 2^(128-k)) :
    let t := block (wideLoopTrace k s) s
    Follows base (wideLoopTrace k s) s ∧ read_pc t = base+236#64 ∧
    (r (.GPR 7) t).toNat = 0 ∧
    (r (.GPR 0) t).toNat =
      (Division.loop (divisor s) n.toNat k
        (r (.GPR 0) s).toNat (join (r (.GPR 5) s) (r (.GPR 6) s))).1 ∧
    join (r (.GPR 5) t) (r (.GPR 6) t) =
      (Division.loop (divisor s) n.toNat k
        (r (.GPR 0) s).toNat (join (r (.GPR 5) s) (r (.GPR 6) s))).2 ∧
    r (.GPR 1) t = r (.GPR 1) s := by
  induction k generalizing s with
  | zero => simpa [wideLoopTrace, block, Follows, Division.loop] using
      (show True ∧ read_pc s = base+236#64 ∧ (r (.GPR 7) s).toNat = 0 ∧
        (r (.GPR 0) s).toNat = (r (.GPR 0) s).toNat ∧
        join (r (.GPR 5) s) (r (.GPR 6) s) = join (r (.GPR 5) s) (r (.GPR 6) s) ∧
        r (.GPR 1) s = r (.GPR 1) s from
        ⟨trivial, by simpa using hp, hn, rfl, rfl, rfl⟩)
  | succ k ih =>
    have hkl : k < 64 := by omega
    have hbit : topBit (r (.GPR 4) s) = (n.toNat / 2^k) % 2 := by
      rw [hs, pending_bit n k hkl]
    have htent : 2*join (r (.GPR 5) s) (r (.GPR 6) s)+topBit (r (.GPR 4) s) <
        2^(128-k) := prefix_bound_step 128 k _ _ (by omega) hb (topBit_lt _)
    have hbound : 2^(128-k) ≤ 2^128 := Nat.pow_le_pow_right (by decide) (by omega)
    obtain ⟨hf, hpc, hcount, hquot, hrem, hstream, h1⟩ :=
      wide_round s base (by simpa using hp) (by omega) (body_q_bound k _ hkl hq)
        hr (Nat.lt_of_lt_of_le htent hbound)
    have hd : divisor (wideRound s) = divisor s := by
      simp only [divisor, wideRound,
        block_frame _ _ (.GPR 2) (by decide : Preserved (.GPR 2)),
        block_frame _ _ (.GPR 3) (by decide : Preserved (.GPR 3))]
    have hn' : (r (.GPR 7) (wideRound s)).toNat = k := by omega
    have hp' : read_pc (wideRound s) =
        if k = 0 then base+236#64 else base+180#64 := by
      rw [hpc, hn]
      by_cases hz : k = 0 <;> simp [hz]
    have hs' : r (.GPR 4) (wideRound s) = pending n k := by
      rw [hstream, hs, pending_next n k hkl]
    have hq' : (r (.GPR 0) (wideRound s)).toNat < 2^(64-k) := by
      rw [hquot]
      exact step_q_bound _ _ _ _ k hkl hq
    have hr' : join (r (.GPR 5) (wideRound s)) (r (.GPR 6) (wideRound s)) <
        divisor (wideRound s) := by
      rw [hrem, hd]
      exact Division.step_remainder_lt _ _ _ _ hr (by omega) (topBit_lt _)
    have hb' : join (r (.GPR 5) (wideRound s)) (r (.GPR 6) (wideRound s)) <
        2^(128-k) := by
      rw [hrem]
      unfold Division.step
      dsimp only
      split <;> dsimp only <;> omega
    obtain ⟨hfollow, hfinalpc, hzero, hfinalq, hfinalr, hfinal1⟩ :=
      ih (wideRound s) (by omega) hn' hp' hs' hq' hr' hb'
    dsimp only
    rw [wideLoopTrace, block_append]
    rw [show block (wideTrace s) s = wideRound s from rfl]
    change Follows base (wideTrace s ++ wideLoopTrace k (wideRound s)) s ∧ _
    refine ⟨(follows_append _ _ _ _).2 ⟨hf, hfollow⟩,
      hfinalpc, hzero, ?_, ?_, hfinal1.trans h1⟩
    · rw [hfinalq, hd, hquot, hrem, hbit]
      rfl
    · rw [hfinalr, hd, hquot, hrem, hbit]
      rfl

end SszArm.Udivti3
