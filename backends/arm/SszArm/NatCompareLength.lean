import SszArm.NatCompareWidth
import SszArm.NatCompareOrder

namespace SszArm.NatCompare

open UintCodec SszNative.Limbs SszNative.NatABI

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def LengthKind.ops : LengthKind → Ordering → List Op
  | .large, .lt => [.p128, .p132, .p136, .p140, .p148, .p152, .p156, .p164]
  | .large, .eq => [.p128, .p132, .p136, .p140, .p148, .p160, .p164, .p168]
  | .large, .gt => [.p128, .p132, .p144, .p148, .p160, .p164]
  | .small, .lt => [.p216, .p220, .p224, .p228, .p236, .p240, .p244, .p252]
  | .small, .eq => [.p216, .p220, .p224, .p228, .p236, .p248, .p252]
  | .small, .gt => [.p216, .p220, .p232, .p236, .p248, .p252]
  | .empty, .lt => [.p264, .p268, .p272, .p276, .p284, .p288, .p292, .p300]
  | .empty, .eq => [.p264, .p268, .p272, .p276, .p284, .p296, .p300]
  | .empty, .gt => [.p264, .p268, .p280, .p284, .p296, .p300]

def orderingWord : Ordering → BitVec 64
  | .lt => 4294967295#64 | .eq => 0#64 | .gt => 1#64

theorem orderingWord_compare (a b : BitVec 64) :
    orderingWord (compare a.toNat b.toNat) = orderWord a b := by
  by_cases hlt : a.toNat < b.toNat <;> by_cases hgt : b.toNat < a.toNat <;>
    simp [orderingWord, orderWord, Nat.compare_eq_ite_lt, hlt, hgt]

theorem length_frame (base : BitVec 64) (s : ArmState) (kind : LengthKind) (ord : Ordering) :
    Frame s (block base (kind.ops ord) s) :=
  readonly_frame base _ _ (by cases kind <;> cases ord <;> decide)

theorem length_zero (base : BitVec 64) (s : ArmState) (kind : LengthKind) (ord : Ordering) :
    r (.GPR 0#5) (block base (kind.ops ord) s) = r (.GPR 0#5) s :=
  block_zero base _ _ (by cases kind <;> cases ord <;> decide)

theorem length_count (base : BitVec 64) (s : ArmState) (kind : LengthKind) (ord : Ordering) :
    r (.GPR 9#5) (block base (kind.ops ord) s) = r (.GPR 9#5) s := by
  cases kind <;> cases ord <;>
    simp [LengthKind.ops, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem length_word (base : BitVec 64) (s : ArmState) (kind : LengthKind) (ord : Ordering) :
    r (.GPR 8#5) (block base (kind.ops ord) s) = orderingWord ord := by
  cases kind <;> cases ord <;>
    simp [LengthKind.ops, orderingWord, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]

theorem length_trace_lt (s : ArmState) (base b : BitVec 64) (kind : LengthKind)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (hb : if kind = .empty then b = 0#64 else r (.GPR 8#5) s = b)
    (hlt : (r (.GPR 9#5) s).toNat < b.toNat) :
    Follows base (kind.ops .lt) s ∧
      read_pc (block base (kind.ops .lt) s) = base + 256#64 := by
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.start := hp
  have hc : (AddWithCarry (r (.GPR 9#5) s) (~~~b) 1#1).2.c ≠ 1#1 := by
    intro h; exact Nat.not_le.mpr hlt ((Udivti3.cmp_carry _ _).mp h)
  have hne : r (.GPR 9#5) s ≠ b := by
    intro h; exact Nat.ne_of_lt hlt (congrArg BitVec.toNat h)
  have hz := (Udivti3.cmp_nonzero (r (.GPR 9#5) s) b).mpr hne
  cases kind <;> cases hb
  all_goals try (exact False.elim (Nat.not_lt_zero _ hlt))
  all_goals
    simp [LengthKind.ops, LengthKind.start, Follows, block, Op.row, Op.effect,
      put, next, Udivti3.compare, Udivti3.next, state_simp_rules, hpc, hc, hz,
      BitVec.add_assoc]

theorem length_trace_eq (s : ArmState) (base b : BitVec 64) (kind : LengthKind)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (hb : if kind = .empty then b = 0#64 else r (.GPR 8#5) s = b)
    (heq : r (.GPR 9#5) s = b) :
    Follows base (kind.ops .eq) s ∧
      read_pc (block base (kind.ops .eq) s) = base + 304#64 := by
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.start := hp
  have hc := (Udivti3.cmp_carry (r (.GPR 9#5) s) b).mpr (by rw [heq]; exact Nat.le_refl _)
  have hz := (Udivti3.cmp_zero (r (.GPR 9#5) s) b).mpr heq
  cases kind with
  | large =>
    cases hb
    simp only [heq] at hc hz
    simp [LengthKind.ops, LengthKind.start, Follows, block, Op.row, Op.effect,
      put, next, Udivti3.compare, Udivti3.next, state_simp_rules, hpc, hc, hz,
      heq, BitVec.add_assoc]
  | small =>
    cases hb
    simp only [heq] at hc hz
    simp [LengthKind.ops, LengthKind.start, Follows, block, Op.row, Op.effect,
      put, next, Udivti3.compare, Udivti3.next, state_simp_rules, hpc, hc, hz,
      heq, BitVec.add_assoc]
  | empty =>
    cases hb
    change (AddWithCarry (r (.GPR 9#5) s) 18446744073709551615#64 1#1).2.z = 1#1 at hz
    rw [heq] at hz
    have hz0 : (AddWithCarry 0#64 18446744073709551615#64 1#1).2.z ≠ 0#1 := by
      rw [hz]
      decide
    simp [LengthKind.ops, LengthKind.start, Follows, block, Op.row, Op.effect,
      put, next, Udivti3.compare, Udivti3.next, state_simp_rules, hpc, hz, hz0,
      heq, BitVec.add_assoc]

theorem length_trace_gt (s : ArmState) (base b : BitVec 64) (kind : LengthKind)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (hb : if kind = .empty then b = 0#64 else r (.GPR 8#5) s = b)
    (hgt : b.toNat < (r (.GPR 9#5) s).toNat) :
    Follows base (kind.ops .gt) s ∧
      read_pc (block base (kind.ops .gt) s) = base + 256#64 := by
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.start := hp
  obtain ⟨hc, hz⟩ := (Udivti3.cmp_high (r (.GPR 9#5) s) b).mpr hgt
  have hne : r (.GPR 9#5) s ≠ b := by
    intro h
    rw [h] at hgt
    exact Nat.lt_irrefl _ hgt
  cases kind with
  | large =>
    cases hb
    simp [LengthKind.ops, LengthKind.start, Follows, block, Op.row, Op.effect,
      put, next, Udivti3.compare, Udivti3.next, state_simp_rules, hpc, hc, hz, hne,
      BitVec.add_assoc]
  | small =>
    cases hb
    simp [LengthKind.ops, LengthKind.start, Follows, block, Op.row, Op.effect,
      put, next, Udivti3.compare, Udivti3.next, state_simp_rules, hpc, hc, hz, hne,
      BitVec.add_assoc]
  | empty =>
    cases hb
    change (AddWithCarry (r (.GPR 9#5) s) 18446744073709551615#64 1#1).2.z = 0#1 at hz
    simp [LengthKind.ops, LengthKind.start, Follows, block, Op.row, Op.effect,
      put, next, Udivti3.compare, Udivti3.next, state_simp_rules, hpc, hz, hne,
      BitVec.add_assoc]

/-- Each original length-dispatch site consumes an opaque flags/path certificate. -/
theorem length_compare (s : ArmState) (base b : BitVec 64) (kind : LengthKind)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (hb : if kind = .empty then b = 0#64 else r (.GPR 8#5) s = b) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      r (.GPR 8#5) t = orderWord (r (.GPR 9#5) s) b ∧
      read_pc t = if r (.GPR 9#5) s = b then base + 304#64 else base + 256#64 := by
  let ord := compare (r (.GPR 9#5) s).toNat b.toNat
  have heq : ord = .eq ↔ r (.GPR 9#5) s = b := by
    constructor
    · intro h; exact BitVec.eq_of_toNat_eq (Nat.compare_eq_eq.mp h)
    · intro h; simp [ord, h]
  have htrace : Follows base (kind.ops ord) s ∧
      read_pc (block base (kind.ops ord) s) = if ord = .eq then base + 304#64 else base + 256#64 := by
    cases hcmp : ord with
    | lt => exact length_trace_lt s base b kind hp hb (Nat.compare_eq_lt.mp hcmp)
    | eq => exact length_trace_eq s base b kind hp hb (BitVec.eq_of_toNat_eq (Nat.compare_eq_eq.mp hcmp))
    | gt => exact length_trace_gt s base b kind hp hb (Nat.compare_eq_gt.mp hcmp)
  refine ⟨(kind.ops ord).length, block base (kind.ops ord) s,
    block_run base (kind.ops ord) s hc he ha htrace.1, length_frame base s kind ord,
    length_zero base s kind ord, length_count base s kind ord,
    (length_word base s kind ord).trans (orderingWord_compare _ _), ?_⟩
  simpa only [heq] using htrace.2

theorem length_return (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 256#64) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ read_pc t = r (.GPR 30#5) s ∧
      (r (.GPR 0#5) t).setWidth 8 = (r (.GPR 8#5) s).setWidth 8 := by
  let ops : List Op := [.p256, .p260]
  have hpc : r .PC s = base + 256#64 := hp
  refine ⟨2, block base ops s, block_run base ops s hc he ha ?_,
    readonly_frame base ops s (by decide), ?_, ?_⟩
  · simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  · exact block_return_pc base [.p256] s .p260 (by decide) (by decide)
  · simp [ops, block, Op.effect, put, next, state_simp_rules, BitVec.setWidth_setWidth_of_le]

end SszArm.NatCompare
