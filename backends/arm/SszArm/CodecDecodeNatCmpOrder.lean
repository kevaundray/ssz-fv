import SszArm.CodecDecodeNatCmpScan
import SszArm.MeasureUintCompare

namespace SszArm.Codec.Decode.NatCmpUsize

open SszNative.NatABI

structure Frame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [0#5, 1#5, 8#5, 9#5, 10#5, 11#5, 12#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ address : BitVec 64,
    address.toNat < (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ address.toNat → t.mem address = s.mem address

theorem Frame.refl (s : ArmState) : Frame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem Frame.sp {s t : ArmState} (frame : Frame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := frame.registers _ (by decide)

theorem Frame.trans {s t u : ArmState} (first : Frame s t) (second : Frame t u) : Frame s u := by
  refine ⟨second.program.trans first.program, second.error.trans first.error,
    fun reg outside => (second.registers reg outside).trans (first.registers reg outside),
    fun reg => (second.vectors reg).trans (first.vectors reg), ?_⟩
  intro address outside
  exact (second.memory address (by simpa only [first.sp] using outside)).trans
    (first.memory address outside)

theorem scan_frame {s t : ArmState} (frame : NatNarrow.Frame s t) : Frame s t := by
  refine ⟨frame.program, frame.error, ?_, frame.vectors, frame.memory⟩
  intro reg outside
  exact frame.registers reg (fun member =>
    outside (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))

def stackOps : List Op := [.p16, .p20, .p44]

theorem readonly_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (members : ∀ op ∈ ops, op ∉ stackOps) : Frame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact Frame.refl s
  | cons op ops ih =>
    have outside := members op List.mem_cons_self
    have frame : Frame s (op.effect base s) := by
      cases op <;> simp_all only [stackOps, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_or, or_self, not_true_eq_false]
      all_goals
        constructor
        · exact Op.program _ _ _
        · exact Op.error _ _ _
        · intro reg outside
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
          simp (disch := simp_all) [Op.effect, put, next, Udivti3.compare,
            Udivti3.next, state_simp_rules]
        · intro reg; exact Op.sfp _ _ _ _
        · intro address outside
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    exact frame.trans (ih _ (fun op member => members op (List.mem_cons_of_mem _ member)))

/-- The real compare tail performs both unsigned 128-bit subtraction orders.
This keeps huge logical inputs out of any machine-word truncation argument. -/
def wideValue (s : ArmState) : Nat := Measure.Uint.pairValue (r (.GPR 1#5) s) (r (.GPR 8#5) s)

def orderOps : Ordering → List Op
  | .lt => [.p120, .p124, .p128, .p132, .p136, .p144, .p148, .p152, .p156, .p160, .p168]
  | .eq => [.p120, .p124, .p128, .p132, .p136, .p144, .p148, .p152, .p164, .p168]
  | .gt => [.p120, .p124, .p128, .p140, .p144, .p148, .p152, .p164, .p168]

theorem order_follows (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 120#64) :
    Follows base (orderOps (compare (wideValue s) (r (.GPR 2#5) s).toNat)) s := by
  have backward := Measure.Uint.pair_compare_carry
    (r (.GPR 2#5) s) 0#64 (r (.GPR 1#5) s) (r (.GPR 8#5) s)
  have forward := Measure.Uint.pair_compare_carry
    (r (.GPR 1#5) s) (r (.GPR 8#5) s) (r (.GPR 2#5) s) 0#64
  change r .PC s = _ at pc
  simp only [Measure.Uint.pairValue, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.mul_zero, Nat.add_zero] at backward forward
  cases order : compare (wideValue s) (r (.GPR 2#5) s).toNat with
  | lt =>
    have less := Nat.compare_eq_lt.mp order
    have back : (AddWithCarry 0#64 (~~~r (.GPR 8#5) s)
        (AddWithCarry (r (.GPR 2#5) s) (~~~r (.GPR 1#5) s) 1#1).2.c).2.c = 1#1 :=
      backward.mpr (by simpa only [wideValue, Measure.Uint.pairValue] using Nat.le_of_lt less)
    have front : (AddWithCarry (r (.GPR 8#5) s) (~~~0#64)
        (AddWithCarry (r (.GPR 1#5) s) (~~~r (.GPR 2#5) s) 1#1).2.c).2.c ≠ 1#1 := by
      intro carry
      have ordered := forward.mp carry
      change (r (.GPR 2#5) s).toNat ≤ wideValue s at ordered
      omega
    change (AddWithCarry (r (.GPR 8#5) s) 18446744073709551615#64
      (AddWithCarry (r (.GPR 1#5) s) (~~~r (.GPR 2#5) s) 1#1).2.c).2.c ≠ 1#1 at front
    simp [orderOps, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
      Udivti3.next, state_simp_rules, pc, back, front, BitVec.add_assoc]
  | eq =>
    have equal := Nat.compare_eq_eq.mp order
    have back := backward.mpr (by simpa only [wideValue, Measure.Uint.pairValue] using Nat.le_of_eq equal)
    have front := forward.mpr (by simpa only [wideValue, Measure.Uint.pairValue] using Nat.le_of_eq equal.symm)
    change (AddWithCarry (r (.GPR 8#5) s) 18446744073709551615#64
      (AddWithCarry (r (.GPR 1#5) s) (~~~r (.GPR 2#5) s) 1#1).2.c).2.c = 1#1 at front
    simp [orderOps, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
      Udivti3.next, state_simp_rules, pc, back, front, BitVec.add_assoc]
  | gt =>
    have greater := Nat.compare_eq_gt.mp order
    have front := forward.mpr (by simpa only [wideValue, Measure.Uint.pairValue] using Nat.le_of_lt greater)
    have back : (AddWithCarry 0#64 (~~~r (.GPR 8#5) s)
        (AddWithCarry (r (.GPR 2#5) s) (~~~r (.GPR 1#5) s) 1#1).2.c).2.c ≠ 1#1 := by
      intro carry
      have ordered := backward.mp carry
      change wideValue s ≤ (r (.GPR 2#5) s).toNat at ordered
      omega
    change (AddWithCarry (r (.GPR 8#5) s) 18446744073709551615#64
      (AddWithCarry (r (.GPR 1#5) s) (~~~r (.GPR 2#5) s) 1#1).2.c).2.c = 1#1 at front
    simp [orderOps, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
      Udivti3.next, state_simp_rules, pc, back, front, BitVec.add_assoc]

theorem order_frame (s : ArmState) (base : BitVec 64) (order : Ordering) :
    Frame s (block base (orderOps order) s) :=
  readonly_frame base (orderOps order) s (by cases order <;> decide)

theorem order_pc (s : ArmState) (base : BitVec 64) (order : Ordering) :
    read_pc (block base (orderOps order) s) = r (.GPR 30#5) s := by
  cases order <;> simp [orderOps, block, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules]

theorem order_byte (s : ArmState) (base : BitVec 64) (order : Ordering) :
    (r (.GPR 0#5) (block base (orderOps order) s)).setWidth 8 = orderingByte order := by
  cases order <;> simp [orderOps, block, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, orderingByte]

theorem return_order (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 120#64) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ read_pc t = r (.GPR 30#5) s ∧
      (r (.GPR 0#5) t).setWidth 8 = orderingByte (compare (wideValue s) (r (.GPR 2#5) s).toNat) := by
  let order := compare (wideValue s) (r (.GPR 2#5) s).toNat
  exact ⟨(orderOps order).length, block base (orderOps order) s,
    block_run base (orderOps order) s code error aligned (order_follows s base pc),
    order_frame s base order, order_pc s base order, order_byte s base order⟩

end SszArm.Codec.Decode.NatCmpUsize
