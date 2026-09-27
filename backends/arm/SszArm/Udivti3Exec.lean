import SszArm.Udivti3Arithmetic

namespace SszArm.Udivti3

open BitVec
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def wordLow (s : ArmState) : BitVec 64 :=
  (AddWithCarry (r (.GPR 6) s) (r (.GPR 6) s)
    (AddWithCarry (r (.GPR 5) s) (r (.GPR 5) s) 0#1).2.c).1

def wordCarry (s : ArmState) : Prop :=
  (AddWithCarry (r (.GPR 6) s) (r (.GPR 6) s)
    (AddWithCarry (r (.GPR 5) s) (r (.GPR 5) s) 0#1).2.c).2.c = 1#1

instance (s : ArmState) : Decidable (wordCarry s) := inferInstanceAs (Decidable (_ = _))

def wordTrace (s : ArmState) : List Nat :=
  if wordCarry s then [22,23,24,25,28,29,30,31]
  else if (r (.GPR 2) s).toNat ≤ (wordLow s).toNat then
    [22,23,24,25,26,27,28,29,30,31]
  else [22,23,24,25,26,27,30,31]

def wordRound (s : ArmState) : ArmState := block (wordTrace s) s

theorem word_take (s : ArmState) :
    (wordCarry s ∨ (r (.GPR 2) s).toNat ≤ (wordLow s).toNat) ↔
      (r (.GPR 2) s).toNat ≤ 2*(r (.GPR 6) s).toNat+topBit (r (.GPR 5) s) := by
  have hc := adc_carry (r (.GPR 6) s) (r (.GPR 6) s)
    (AddWithCarry (r (.GPR 5) s) (r (.GPR 5) s) 0#1).2.c
  rw [double_carry] at hc
  have hd := (r (.GPR 2) s).isLt
  have hr := (r (.GPR 6) s).isLt
  have hb := topBit_lt (r (.GPR 5) s)
  simp only [wordCarry, wordLow, hc, adc_value, double_carry_word,
    BitVec.toNat_add, BitVec.toNat_ofNat, radix]
  omega

/-- Every overflow and nonoverflow branch of the word body, including SUBS/B.NE. -/
theorem word_round (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 88#64)
    (hk : 0 < (r (.GPR 7) s).toNat)
    (hq : 2*(r (.GPR 0) s).toNat+1 < radix)
    (hr : (r (.GPR 6) s).toNat < (r (.GPR 2) s).toNat) :
    Follows base (wordTrace s) s ∧
    read_pc (wordRound s) =
      (if (r (.GPR 7) s).toNat = 1 then base+128#64 else base+88#64) ∧
    (r (.GPR 7) (wordRound s)).toNat = (r (.GPR 7) s).toNat-1 ∧
    (r (.GPR 0) (wordRound s)).toNat =
      (Division.step (r (.GPR 2) s).toNat (topBit (r (.GPR 5) s))
        (r (.GPR 0) s).toNat (r (.GPR 6) s).toNat).1 ∧
    (r (.GPR 6) (wordRound s)).toNat =
      (Division.step (r (.GPR 2) s).toNat (topBit (r (.GPR 5) s))
        (r (.GPR 0) s).toNat (r (.GPR 6) s).toNat).2 ∧
    r (.GPR 5) (wordRound s) = r (.GPR 5) s + r (.GPR 5) s ∧
    r (.GPR 1) (wordRound s) = r (.GPR 1) s ∧
    r (.GPR 4) (wordRound s) = r (.GPR 4) s ∧
    r (.GPR 8) (wordRound s) = r (.GPR 8) s := by
  have ht := word_take s
  have hc := adc_carry (r (.GPR 6) s) (r (.GPR 6) s)
    (AddWithCarry (r (.GPR 5) s) (r (.GPR 5) s) 0#1).2.c
  rw [double_carry] at hc
  have hv := word_step (r (.GPR 6) s) (r (.GPR 2) s) (r (.GPR 5) s) hr
  have hb := topBit_lt (r (.GPR 5) s)
  have hn := (r (.GPR 7) s).isLt
  have hz : (r (.GPR 7) s).toNat = 1 ↔ r (.GPR 7) s = 1#64 := by bv_omega
  change r .PC s = base+88#64 at hp
  dsimp only [radix] at *
  by_cases carry : wordCarry s <;>
    by_cases take : (r (.GPR 2) s).toNat ≤ (wordLow s).toNat <;>
    by_cases last : (r (.GPR 7) s).toNat = 1
  all_goals
    simp_all (config := {decide := true, instances := true})
      [wordRound, wordTrace, block, Follows, instruction, next, put, compare,
       flagged, branch, state_simp_rules, cmp_carry,
       wordCarry, wordLow, Division.step, BitVec.add_assoc, apply_ite, read_pc,
       Nat.two_mul, Nat.add_assoc, ← Nat.not_lt, -BitVec.not_lt]
    all_goals first | assumption | bv_omega

def wideLow (s : ArmState) : BitVec 64 :=
  (AddWithCarry (r (.GPR 5) s) (r (.GPR 5) s)
    (AddWithCarry (r (.GPR 4) s) (r (.GPR 4) s) 0#1).2.c).1

def wideHigh (s : ArmState) : BitVec 64 :=
  (AddWithCarry (r (.GPR 6) s) (r (.GPR 6) s)
    (AddWithCarry (r (.GPR 5) s) (r (.GPR 5) s)
      (AddWithCarry (r (.GPR 4) s) (r (.GPR 4) s) 0#1).2.c).2.c).1

def wideTrace (s : ArmState) : List Nat :=
  [45,46,47,48,49,50] ++
  if (r (.GPR 3) s).toNat < (wideHigh s).toNat then [54,55,56,57,58]
  else [51] ++
    if (wideHigh s).toNat < (r (.GPR 3) s).toNat then [57,58]
    else [52,53] ++
      if (wideLow s).toNat < (r (.GPR 2) s).toNat then [57,58]
      else [54,55,56,57,58]

def wideRound (s : ArmState) : ArmState := block (wideTrace s) s

/-- The wide body compares both words and propagates the actual low subtraction borrow. -/
theorem wide_round (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 180#64)
    (hk : 0 < (r (.GPR 7) s).toNat)
    (hq : 2*(r (.GPR 0) s).toNat+1 < radix)
    (_hr : join (r (.GPR 5) s) (r (.GPR 6) s) < divisor s)
    (hb : 2*join (r (.GPR 5) s) (r (.GPR 6) s)+topBit (r (.GPR 4) s) < 2^128) :
    Follows base (wideTrace s) s ∧
    read_pc (wideRound s) =
      (if (r (.GPR 7) s).toNat = 1 then base+236#64 else base+180#64) ∧
    (r (.GPR 7) (wideRound s)).toNat = (r (.GPR 7) s).toNat-1 ∧
    (r (.GPR 0) (wideRound s)).toNat =
      (Division.step (divisor s) (topBit (r (.GPR 4) s))
        (r (.GPR 0) s).toNat (join (r (.GPR 5) s) (r (.GPR 6) s))).1 ∧
    join (r (.GPR 5) (wideRound s)) (r (.GPR 6) (wideRound s)) =
      (Division.step (divisor s) (topBit (r (.GPR 4) s))
        (r (.GPR 0) s).toNat (join (r (.GPR 5) s) (r (.GPR 6) s))).2 ∧
    r (.GPR 4) (wideRound s) = r (.GPR 4) s + r (.GPR 4) s ∧
    r (.GPR 1) (wideRound s) = r (.GPR 1) s := by
  have hv : join (wideLow s) (wideHigh s) =
      2*join (r (.GPR 5) s) (r (.GPR 6) s)+topBit (r (.GPR 4) s) :=
    wide_double _ _ _ hb
  have hcmp := join_lt_iff (wideLow s) (wideHigh s) (r (.GPR 2) s) (r (.GPR 3) s)
  have hsub := wide_subtract (wideLow s) (wideHigh s) (r (.GPR 2) s) (r (.GPR 3) s)
  have hbit := topBit_lt (r (.GPR 4) s)
  have hn := (r (.GPR 7) s).isLt
  have hz : (r (.GPR 7) s).toNat = 1 ↔ r (.GPR 7) s = 1#64 := by bv_omega
  have heq : (wideHigh s).toNat = (r (.GPR 3) s).toNat ↔
      wideHigh s = r (.GPR 3) s :=
    ⟨BitVec.eq_of_toNat_eq, congrArg BitVec.toNat⟩
  have hsame := eq_iff_order (wideHigh s) (r (.GPR 3) s)
  change r .PC s = base+180#64 at hp
  dsimp only [radix] at *
  by_cases high : (r (.GPR 3) s).toNat < (wideHigh s).toNat <;>
    by_cases low : (wideHigh s).toNat < (r (.GPR 3) s).toNat <;>
    by_cases word : (wideLow s).toNat < (r (.GPR 2) s).toNat <;>
    by_cases last : (r (.GPR 7) s).toNat = 1
  all_goals
    have take : (divisor s ≤ join (wideLow s) (wideHigh s)) ↔
        ¬ ((wideHigh s).toNat < (r (.GPR 3) s).toNat ∨
          (wideHigh s).toNat = (r (.GPR 3) s).toNat ∧
            (wideLow s).toNat < (r (.GPR 2) s).toNat) := by
      dsimp only [divisor]
      rw [heq, ← hcmp]
      exact Nat.not_lt.symm
    simp_all (config := {decide := true, instances := true})
      [wideRound, wideTrace, block, Follows, instruction, next, put, compare,
       flagged, branch, state_simp_rules, cmp_carry,
       cmp_nonzero, wideLow, wideHigh, Division.step, BitVec.add_assoc, read_pc,
       divisor, Nat.two_mul, Nat.add_assoc, ← Nat.not_lt, -BitVec.not_lt]
    all_goals first | assumption | bv_omega

/-- The entry comparison deliberately compares high words before low words. -/
def entryTrace (s : ArmState) : List Nat :=
  if (r (.GPR 1) s).toNat < (r (.GPR 3) s).toNat then [0,1]
  else if (r (.GPR 3) s).toNat < (r (.GPR 1) s).toNat then [0,1,2]
  else [0,1,2,3,4]

def entry (s : ArmState) : ArmState := block (entryTrace s) s

theorem entry_data (s : ArmState) (base : BitVec 64) (hp : read_pc s = base) :
    Follows base (entryTrace s) s ∧
    read_pc (entry s) = (if numerator s < divisor s then base+248#64 else base+20#64) ∧
    (∀ i, r (.GPR i) (entry s) = r (.GPR i) s) := by
  have hc := join_lt_iff (r (.GPR 0) s) (r (.GPR 1) s)
    (r (.GPR 2) s) (r (.GPR 3) s)
  have hsame := eq_iff_order (r (.GPR 1) s) (r (.GPR 3) s)
  change r .PC s = base at hp
  by_cases high : (r (.GPR 1) s).toNat < (r (.GPR 3) s).toNat <;>
    by_cases low : (r (.GPR 3) s).toNat < (r (.GPR 1) s).toNat <;>
    by_cases word : (r (.GPR 0) s).toNat < (r (.GPR 2) s).toNat
  all_goals
    simp_all (config := {decide := true, instances := true})
      [entry, entryTrace, block, Follows, instruction, next, compare,
       branch, state_simp_rules, cmp_carry,
       cmp_nonzero, numerator, divisor, BitVec.add_assoc, read_pc,
       ← Nat.not_lt, -BitVec.not_lt]
    all_goals first | omega | bv_omega

/-- Setup for either the low-word pass or the high-word-first pass. -/
def wordSetup (s : ArmState) : List Nat :=
  [5,6,7,8,9,10,11,12] ++
    if (r (.GPR 1) s).toNat < (r (.GPR 2) s).toNat then [13,14,15,16,17]
    else [18,19,20,21]

theorem word_setup (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base+20#64) (hh : r (.GPR 3) s = 0#64)
    (hd : r (.GPR 2) s ≠ 1#64) :
    let t := block (wordSetup s) s
    Follows base (wordSetup s) s ∧ read_pc t = base+88#64 ∧
    r (.GPR 0) t = 0#64 ∧ r (.GPR 1) t = 0#64 ∧
    r (.GPR 4) t = r (.GPR 0) s ∧ r (.GPR 7) t = 64#64 ∧
    r (.GPR 5) t = (if (r (.GPR 1) s).toNat < (r (.GPR 2) s).toNat
      then r (.GPR 0) s else r (.GPR 1) s) ∧
    r (.GPR 6) t = (if (r (.GPR 1) s).toNat < (r (.GPR 2) s).toNat
      then r (.GPR 1) s else 0#64) ∧
    r (.GPR 8) t = (if (r (.GPR 1) s).toNat < (r (.GPR 2) s).toNat
      then 0#64 else 1#64) := by
  change r .PC s = base+20#64 at hp
  by_cases high : (r (.GPR 1) s).toNat < (r (.GPR 2) s).toNat
  all_goals
    simp_all (config := {decide := true, instances := true})
      [wordSetup, block, Follows, instruction, next, put, compare,
       branch, state_simp_rules, cmp_carry, BitVec.add_assoc, read_pc,
       ← Nat.not_lt, -BitVec.not_lt]
    all_goals bv_omega

theorem wide_setup (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base+20#64) (hh : r (.GPR 3) s ≠ 0#64) :
    let t := block [5,40,41,42,43,44] s
    Follows base [5,40,41,42,43,44] s ∧ read_pc t = base+180#64 ∧
    r (.GPR 0) t = 0#64 ∧ r (.GPR 4) t = r (.GPR 0) s ∧
    r (.GPR 5) t = r (.GPR 1) s ∧ r (.GPR 6) t = 0#64 ∧
    r (.GPR 7) t = 64#64 := by
  change r .PC s = base+20#64 at hp
  simp_all (config := {decide := true, instances := true})
    [block, Follows, instruction, next, put, branch,
     state_simp_rules, BitVec.add_assoc, read_pc]
  all_goals bv_omega

theorem second_setup (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base+128#64) (hh : r (.GPR 8) s = 1#64) :
    let t := block [32,33,34,35,36,37,38] s
    Follows base [32,33,34,35,36,37,38] s ∧ read_pc t = base+88#64 ∧
    r (.GPR 0) t = 0#64 ∧ r (.GPR 1) t = r (.GPR 0) s ∧
    r (.GPR 5) t = r (.GPR 4) s ∧ r (.GPR 6) t = r (.GPR 6) s ∧
    r (.GPR 7) t = 64#64 ∧ r (.GPR 8) t = 0#64 := by
  change r .PC s = base+128#64 at hp
  simp_all (config := {decide := true, instances := true})
    [block, Follows, instruction, next, put, branch,
     state_simp_rules, BitVec.add_assoc, read_pc]
  all_goals bv_omega

end SszArm.Udivti3
