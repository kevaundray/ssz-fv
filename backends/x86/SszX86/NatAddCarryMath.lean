import SszX86.NatAddCore
import SszX86.Udivti3Math

namespace SszX86.NatAdd.Carry
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The two ADDs and SETB/ADC in the general limb loop. -/
theorem two_adds (left right : BitVec 64) (carry : Nat) (hc : carry ≤ 1) :
    BitVec.ofNat 64 carry + right + left = (LimbAdd.step left right carry).1 ∧
    BitVec.ofNat 64 (Udivti3.addFlags (BitVec.ofNat 64 carry) right).cf.toNat +
      BitVec.ofNat 64 (Udivti3.addFlags (BitVec.ofNat 64 carry + right) left).cf.toNat =
        BitVec.ofNat 64 (LimbAdd.step left right carry).2 := by
  have hl := left.isLt
  have hr := right.isLt
  have hcarry : carry < 2^64 := by omega
  have hv : (BitVec.ofNat 64 carry).toNat = carry := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcarry]
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [LimbAdd.step, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_add_mod]
    congr 1
    omega
  · rw [Udivti3.addFlags_cf, Udivti3.addFlags_cf, hv]
    simp only [BitVec.toNat_add, hv]
    by_cases first : 2^64 ≤ carry + right.toNat <;>
      by_cases second : 2^64 ≤ (carry + right.toNat) % 2^64 + left.toNat
    all_goals
      simp only [Udivti3.radix, first, second, decide_true, decide_false,
        Bool.toNat_true, Bool.toNat_false]
      apply BitVec.eq_of_toNat_eq
      simp only [LimbAdd.step, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega

/-- The one-ADD paired loop is the same carry step with an absent left limb. -/
theorem one_add (right : BitVec 64) (carry : Nat) (hc : carry ≤ 1) :
    BitVec.ofNat 64 carry + right = (LimbAdd.step 0 right carry).1 ∧
    (Udivti3.addFlags (BitVec.ofNat 64 carry) right).cf.toNat =
      (LimbAdd.step 0 right carry).2 := by
  have hr := right.isLt
  have hcarry : carry < 2^64 := by omega
  have zeroNat : (0 : BitVec 64).toNat = 0 := by decide
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [LimbAdd.step, BitVec.toNat_add, BitVec.toNat_ofNat,
      zeroNat, Nat.zero_add, Nat.mod_eq_of_lt hcarry]
    rw [Nat.add_comm]
  · rw [Udivti3.addFlags_cf]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcarry, LimbAdd.step,
      zeroNat, Nat.zero_add, Udivti3.radix]
    by_cases overflow : 2^64 ≤ carry + right.toNat <;> simp [overflow] <;> omega

/-- The original lists, rather than normalized storage, drive every load. -/
abbrev limbAt (words : List (BitVec 64)) (index : Nat) : BitVec 64 :=
  words[index]?.getD 0

/-- A small left operand has no physical load at any positive limb index. -/
theorem small_limbAt (limb : BitVec 64) (index : Nat) (hi : 0 < index) :
    limbAt (NatOperand.small limb).words index = 0 := by
  cases index with
  | zero => omega
  | succ index => simp [NatOperand.words, limbAt]

/-- The both-small zero-fill block is impossible at significant width at least two. -/
theorem not_both_small (left right : NatOperand) (m : DataMem)
    (hl : left.At (widthLoad m)) (hr : right.At (widthLoad m))
    (hc : 2 ≤ SszNative.NatAdd.count left right) :
    left.pointer ≠ 0 ∨ right.pointer ≠ 0 := by
  cases left with
  | small a =>
    cases right with
    | small b =>
      simp only [SszNative.NatAdd.count, NatOperand.wordCount, NatOperand.words,
        NatCompare.single_sig] at hc
      split at hc <;> split at hc <;> omega
    | large p words =>
      right
      intro zero
      have positive := hr.1
      simp only [NatOperand.pointer] at zero
      simp [zero] at positive
  | large p words =>
    left
    intro zero
    have positive := hl.1
    simp only [NatOperand.pointer] at zero
    simp [zero] at positive

/-- Exact output separation only: immutable inputs need not be separated. -/
def Apart (operand : NatOperand) (dst : BitVec 64) (capacity : Nat) : Prop :=
  match operand with
  | .small _ => True
  | .large p words => Large.Disjoint p dst (8 * words.length) capacity

/-- Sequential output stores preserve every original limb, including high zeros. -/
theorem fill_preserves (m : DataMem) (operand : NatOperand) (dst : BitVec 64)
    (index capacity : Nat) (words : List (BitVec 64))
    (owned : operand.At (widthLoad m)) (apart : Apart operand dst capacity)
    (bound : 8 * (index + words.length) ≤ capacity) :
    operand.At (widthLoad (Large.fillMem m dst index words)) := by
  cases operand with
  | small limb => trivial
  | large pointer original =>
    obtain ⟨positive, aligned, room, stored⟩ := owned
    refine ⟨positive, aligned, room, ?_⟩
    intro i
    rw [show widthLoad (Large.fillMem m dst index words)
        (pointer.toNat + 8*i.val) 8 = widthLoad m (pointer.toNat + 8*i.val) 8 from ?_]
    · exact stored i
    unfold widthLoad
    congr 1
    apply memmove_loadInt_congr
    intro j hj
    rw [width_address, memmove_addr_add]
    apply Large.fill_frame
    intro k hlo hhi eq
    exact apart (8*i.val+j) (by have := i.isLt; omega) k (by omega) eq

/-- The store sequence is associative, at the actual limb addresses. -/
theorem fill_append (m : DataMem) (dst : BitVec 64) (index : Nat)
    (front rest : List (BitVec 64)) :
    Large.fillMem m dst index (front ++ rest) =
      Large.fillMem (Large.fillMem m dst index front) dst (index + front.length) rest := by
  induction front generalizing m index with
  | nil => simp [Large.fillMem]
  | cons first rest ih =>
    simp only [List.cons_append, Large.fillMem, ih, List.length_cons]
    congr 1 <;> omega

/-- Arbitrary-count loop splitting, used for both the scalar and paired loops. -/
theorem loop_split (front rest index : Nat) (left right : List (BitVec 64))
    (carry : Nat) :
    (LimbAdd.loop (front + rest) (left.drop index) (right.drop index) carry).1 =
      (LimbAdd.loop front (left.drop index) (right.drop index) carry).1 ++
      (LimbAdd.loop rest (left.drop (index + front)) (right.drop (index + front))
        (LimbAdd.loop front (left.drop index) (right.drop index) carry).2).1 := by
  induction front generalizing index carry with
  | zero => simp [LimbAdd.loop]
  | succ front ih =>
    rw [show front + 1 + rest = (front + rest) + 1 by omega]
    simp only [LimbAdd.loop_indexed_succ]
    rw [ih]
    simp only [List.cons_append,
      show index + 1 + front = index + (front + 1) by omega]

end SszX86.NatAdd.Carry
