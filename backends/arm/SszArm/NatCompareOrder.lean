import SszArm.NatCompareBlocks

namespace SszArm.NatCompare

open UintCodec SszNative.NatABI

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

@[simp] theorem cmp_zero_bit (a b : BitVec 64) :
    (AddWithCarry a (~~~b) 1#1).2.z = 0#1 ↔ a ≠ b :=
  Udivti3.cmp_nonzero a b

@[simp] theorem count_zero_bit (a : BitVec 64) :
    (AddWithCarry a 1#64 0#1).2.z = 1#1 ↔ a + 1#64 = 0#64 := by
  change (if (AddWithCarry a 1#64 0#1).1 = 0#64 then 1#1 else 0#1) = 1#1 ↔ _
  rw [fst_AddWithCarry_eq_add]
  simp

def orderWord (a b : BitVec 64) : BitVec 64 :=
  if a.toNat < b.toNat then 4294967295#64 else if b.toNat < a.toNat then 1#64 else 0#64

theorem orderWord_low (a b : BitVec 64) :
    (orderWord a b).setWidth 8 = orderingByte (compare a.toNat b.toNat) := by
  by_cases hlt : a.toNat < b.toNat <;> by_cases hgt : b.toNat < a.toNat
  all_goals simp [orderWord, orderingByte, Nat.compare_eq_ite_lt, hlt, hgt]

def orderOps : Ordering → List Op
  | .lt => [.p548, .p552, .p556, .p560, .p568, .p572, .p576, .p584]
  | .eq => [.p548, .p552, .p556, .p560, .p568, .p580, .p584]
  | .gt => [.p548, .p552, .p564, .p568, .p580, .p584]

/-- A RET observation needs only the already opaque prefix frame. -/
theorem block_return_pc (base : BitVec 64) (ops : List Op) (s : ArmState) (ret : Op)
    (hret : ret ∈ [.p260, .p584, .p708])
    (hops : ∀ op ∈ ops, op ∉ stackOps) :
    read_pc (block base (ops ++ [ret]) s) = r (.GPR 30#5) s := by
  have hf := readonly_frame base ops s hops
  have hr : ∀ t : ArmState, read_pc (ret.effect base t) = r (.GPR 30#5) t := by
    intro t
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hret
    rcases hret with rfl | rfl | rfl <;>
      simp [Op.effect, read_pc, r, w, read_base_pc, write_base_pc]
  change read_pc (List.foldl (fun t op => op.effect base t) s (ops ++ [ret])) = _
  rw [List.foldl_append]
  change read_pc (ret.effect base (block base ops s)) = _
  rw [hr]
  exact hf.registers 30#5 (by decide)

theorem order_frame (base : BitVec 64) (s : ArmState) (ord : Ordering) :
    Frame s (block base (orderOps ord) s) :=
  readonly_frame base _ _ (by cases ord <;> decide)

theorem order_pc (base : BitVec 64) (s : ArmState) (ord : Ordering) :
    read_pc (block base (orderOps ord) s) = r (.GPR 30#5) s := by
  cases ord with
  | lt =>
    exact block_return_pc base [.p548, .p552, .p556, .p560, .p568, .p572, .p576]
      s .p584 (by decide) (by decide)
  | eq =>
    exact block_return_pc base [.p548, .p552, .p556, .p560, .p568, .p580]
      s .p584 (by decide) (by decide)
  | gt =>
    exact block_return_pc base [.p548, .p552, .p564, .p568, .p580]
      s .p584 (by decide) (by decide)

theorem order_byte (base : BitVec 64) (s : ArmState) (ord : Ordering) :
    (r (.GPR 0#5) (block base (orderOps ord) s)).setWidth 8 = orderingByte ord := by
  cases ord <;>
    simp [orderOps, block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, orderingByte]

theorem order_follows_lt (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 548#64)
    (hlt : (r (.GPR 8#5) s).toNat < (r (.GPR 10#5) s).toNat) :
    Follows base (orderOps .lt) s := by
  have hpc : r .PC s = base + 548#64 := hp
  have hc : (AddWithCarry (r (.GPR 8#5) s) (~~~r (.GPR 10#5) s) 1#1).2.c ≠ 1#1 := by
    intro h
    exact Nat.not_le.mpr hlt ((Udivti3.cmp_carry _ _).mp h)
  simp [orderOps, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, hpc, hc, BitVec.add_assoc]

theorem order_follows_eq (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 548#64)
    (heq : r (.GPR 8#5) s = r (.GPR 10#5) s) :
    Follows base (orderOps .eq) s := by
  have hpc : r .PC s = base + 548#64 := hp
  have hc : (AddWithCarry (r (.GPR 8#5) s) (~~~r (.GPR 10#5) s) 1#1).2.c = 1#1 :=
    (Udivti3.cmp_carry _ _).mpr (by rw [heq]; exact Nat.le_refl _)
  have hz : (AddWithCarry (r (.GPR 8#5) s) (~~~r (.GPR 10#5) s) 1#1).2.z = 1#1 :=
    (Udivti3.cmp_zero _ _).mpr heq
  simp [orderOps, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, hpc, hc, hz, BitVec.add_assoc]

theorem order_follows_gt (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 548#64)
    (hgt : (r (.GPR 10#5) s).toNat < (r (.GPR 8#5) s).toNat) :
    Follows base (orderOps .gt) s := by
  have hpc : r .PC s = base + 548#64 := hp
  obtain ⟨hc, hz⟩ := (Udivti3.cmp_high (r (.GPR 8#5) s) (r (.GPR 10#5) s)).mpr hgt
  simp [orderOps, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, hpc, hc, hz, BitVec.add_assoc]

/-- Original comparison, byte result, and RET, composed from opaque certificates. -/
theorem return_order (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 548#64) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ read_pc t = r (.GPR 30#5) s ∧
      (r (.GPR 0#5) t).setWidth 8 =
        orderingByte (compare (r (.GPR 8#5) s).toNat (r (.GPR 10#5) s).toNat) := by
  let ord := compare (r (.GPR 8#5) s).toNat (r (.GPR 10#5) s).toNat
  have hfollow : Follows base (orderOps ord) s := by
    cases hcmp : ord with
    | lt => exact order_follows_lt s base hp (Nat.compare_eq_lt.mp hcmp)
    | eq => exact order_follows_eq s base hp (BitVec.eq_of_toNat_eq (Nat.compare_eq_eq.mp hcmp))
    | gt => exact order_follows_gt s base hp (Nat.compare_eq_gt.mp hcmp)
  exact ⟨(orderOps ord).length, block base (orderOps ord) s,
    block_run base (orderOps ord) s hc he ha hfollow, order_frame base s ord,
    order_pc base s ord, order_byte base s ord⟩

theorem return_equal (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 700#64) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ read_pc t = r (.GPR 30#5) s ∧
      (r (.GPR 0#5) t).setWidth 8 = orderingByte .eq := by
  let ops : List Op := [.p700, .p704, .p708]
  have hpc : r .PC s = base + 700#64 := hp
  refine ⟨3, block base ops s, block_run base ops s hc he ha ?_,
    readonly_frame base ops s (by decide), ?_, ?_⟩
  · simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  · simp [ops, block, Op.effect, put, next, state_simp_rules, r, w,
      read_base_pc, write_base_pc, read_base_gpr, write_base_gpr, read_store, write_store]
  · simp [ops, block, Op.effect, put, next, state_simp_rules, orderingByte]

end SszArm.NatCompare
