import SszArm.ByteViewVectorExec
import SszArm.ByteViewWidthMemory

namespace SszArm.ByteView.Bounded

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

inductive Op where
  | p688 | p692 | p696 | p700 | p704 | p708 | p712 | p716 | p720 | p724 | p728 | p732 | p736 | p740 | p744 | p748 | p752 | p756 | p760 | p764 | p768 | p772 | p776 | p780 | p784 | p788 | p792 | p796 | p2596 | p2600 | p2604 | p2608 | p2612 | p2616 | p2620 | p2624 | p2628 | p2632 | p2636 | p2640 | p2644 | p2648 | p2652 | p2656 | p2660 | p2664 | p2668 | p2672 | p2676 | p2680 | p2684 | p2688 | p2692 | p2696 | p2700 | p3480 | p3484 | p3488 | p3492 | p3496 | p3500 | p3504 | p3508 | p3512 | p3516 | p3520 | p3524 | p3528 | p3532 | p3536 | p3540 | p3544 | p3548 | p3552 | p3556 | p3560 | p3564 | p3568 | p3572
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p688 => (688, 0xa940a428#32)
  | .p692 => (692, 0xf100007f#32)
  | .p696 => (696, 0x54000061#32)
  | .p700 => (700, 0x5280000a#32)
  | .p704 => (704, 0x14000002#32)
  | .p708 => (708, 0x5280002a#32)
  | .p712 => (712, 0xb4003ae8#32)
  | .p716 => (716, 0xd100052b#32)
  | .p720 => (720, 0xb100057f#32)
  | .p724 => (724, 0x54005620#32)
  | .p728 => (728, 0xd10043ff#32)
  | .p732 => (732, 0xf90003e9#32)
  | .p736 => (736, 0xaa0b03e9#32)
  | .p740 => (740, 0xd37df129#32)
  | .p744 => (744, 0x8b090109#32)
  | .p748 => (748, 0xf940012c#32)
  | .p752 => (752, 0xf94003e9#32)
  | .p756 => (756, 0x910043ff#32)
  | .p760 => (760, 0xd100056b#32)
  | .p764 => (764, 0xb4fffeac#32)
  | .p768 => (768, 0x9100096b#32)
  | .p772 => (772, 0xeb0a017f#32)
  | .p776 => (776, 0x54000063#32)
  | .p780 => (780, 0x5280000a#32)
  | .p784 => (784, 0x14000002#32)
  | .p788 => (788, 0x5280002a#32)
  | .p792 => (792, 0x540054c0#32)
  | .p796 => (796, 0x140002ad#32)
  | .p2596 => (2596, 0xf100007f#32)
  | .p2600 => (2600, 0x54000061#32)
  | .p2604 => (2604, 0x5280000a#32)
  | .p2608 => (2608, 0x14000002#32)
  | .p2612 => (2612, 0x5280002a#32)
  | .p2616 => (2616, 0xf100013f#32)
  | .p2620 => (2620, 0x54000061#32)
  | .p2624 => (2624, 0x5280000b#32)
  | .p2628 => (2628, 0x14000002#32)
  | .p2632 => (2632, 0x5280002b#32)
  | .p2636 => (2636, 0x4a0b014b#32)
  | .p2640 => (2640, 0x1a8a13ea#32)
  | .p2644 => (2644, 0xd10043ff#32)
  | .p2648 => (2648, 0xf90003e9#32)
  | .p2652 => (2652, 0x12000169#32)
  | .p2656 => (2656, 0x35000089#32)
  | .p2660 => (2660, 0xf94003e9#32)
  | .p2664 => (2664, 0x910043ff#32)
  | .p2668 => (2668, 0x14000004#32)
  | .p2672 => (2672, 0xf94003e9#32)
  | .p2676 => (2676, 0x910043ff#32)
  | .p2680 => (2680, 0x140000d6#32)
  | .p2684 => (2684, 0xb4003883#32)
  | .p2688 => (2688, 0xeb09007f#32)
  | .p2692 => (2692, 0xaa0903ea#32)
  | .p2696 => (2696, 0x540019e1#32)
  | .p2700 => (2700, 0x140001c0#32)
  | .p3480 => (3480, 0xeb0a03ff#32)
  | .p3484 => (3484, 0x54000063#32)
  | .p3488 => (3488, 0x5280000a#32)
  | .p3492 => (3492, 0x14000002#32)
  | .p3496 => (3496, 0x5280002a#32)
  | .p3500 => (3500, 0x54000121#32)
  | .p3504 => (3504, 0xb4001ee3#32)
  | .p3508 => (3508, 0xb4000229#32)
  | .p3512 => (3512, 0xf940010a#32)
  | .p3516 => (3516, 0xeb0a007f#32)
  | .p3520 => (3520, 0x54001e60#32)
  | .p3524 => (3524, 0xeb0a007f#32)
  | .p3528 => (3528, 0x54001e29#32)
  | .p3532 => (3532, 0x1400000b#32)
  | .p3536 => (3536, 0xd10043ff#32)
  | .p3540 => (3540, 0xf90003e9#32)
  | .p3544 => (3544, 0x12000149#32)
  | .p3548 => (3548, 0x34000089#32)
  | .p3552 => (3552, 0xf94003e9#32)
  | .p3556 => (3556, 0x910043ff#32)
  | .p3560 => (3560, 0x14000004#32)
  | .p3564 => (3564, 0xf94003e9#32)
  | .p3568 => (3568, 0x910043ff#32)
  | .p3572 => (3572, 0x140000e6#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p688, s => Vector.widthLoaded s
  | .p692, s => Udivti3.compare (r (.GPR 3#5) s) (0#64) s
  | .p696, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 708#64 else base + 700#64) s
  | .p700, s => put 10 (0#64) s
  | .p704, s => w .PC (base + 712#64) s
  | .p708, s => put 10 (1#64) s
  | .p712, s => w .PC (if r (.GPR 8#5) s = 0#64 then base + 2596#64 else base + 716#64) s
  | .p716, s => put 11 ((r (.GPR 9#5) s) - (1#64)) s
  | .p720, s => write_pstate (AddWithCarry (r (.GPR 11#5) s) (1#64) 0#1).2 (next s)
  | .p724, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 3480#64 else base + 728#64) s
  | .p728, s => put 31 ((r (.GPR 31#5) s) - (16#64)) s
  | .p732, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p736, s => put 9 (r (.GPR 11#5) s) s
  | .p740, s => put 9 ((r (.GPR 9#5) s) <<< 3) s
  | .p744, s => put 9 ((r (.GPR 8#5) s) + (r (.GPR 9#5) s)) s
  | .p748, s => put 12 (read_mem_bytes 8 (r (.GPR 9#5) s) s) s
  | .p752, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p756, s => put 31 ((r (.GPR 31#5) s) + (16#64)) s
  | .p760, s => put 11 ((r (.GPR 11#5) s) - (1#64)) s
  | .p764, s => w .PC (if r (.GPR 12#5) s = 0#64 then base + 720#64 else base + 768#64) s
  | .p768, s => put 11 ((r (.GPR 11#5) s) + (2#64)) s
  | .p772, s => Udivti3.compare (r (.GPR 11#5) s) (r (.GPR 10#5) s) s
  | .p776, s => w .PC (if r (.FLAG .C) s ≠ 1#1 then base + 788#64 else base + 780#64) s
  | .p780, s => put 10 (0#64) s
  | .p784, s => w .PC (base + 792#64) s
  | .p788, s => put 10 (1#64) s
  | .p792, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 3504#64 else base + 796#64) s
  | .p796, s => w .PC (base + 3536#64) s
  | .p2596, s => Udivti3.compare (r (.GPR 3#5) s) (0#64) s
  | .p2600, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 2612#64 else base + 2604#64) s
  | .p2604, s => put 10 (0#64) s
  | .p2608, s => w .PC (base + 2616#64) s
  | .p2612, s => put 10 (1#64) s
  | .p2616, s => Udivti3.compare (r (.GPR 9#5) s) (0#64) s
  | .p2620, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 2632#64 else base + 2624#64) s
  | .p2624, s => put 11 (0#64) s
  | .p2628, s => w .PC (base + 2636#64) s
  | .p2632, s => put 11 (1#64) s
  | .p2636, s => put 11 ((((r (.GPR 10#5) s).setWidth 32) ^^^ ((r (.GPR 11#5) s).setWidth 32)).setWidth 64) s
  | .p2640, s => put 10 (if r (.FLAG .Z) s = 1#1 then ((r (.GPR 10#5) s).setWidth 32).setWidth 64 else 0#64) s
  | .p2644, s => put 31 ((r (.GPR 31#5) s) - (16#64)) s
  | .p2648, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p2652, s => put 9 ((((r (.GPR 11#5) s).setWidth 32) &&& 1#32).setWidth 64) s
  | .p2656, s => w .PC (if (r (.GPR 9#5) s).setWidth 32 ≠ 0#32 then base + 2672#64 else base + 2660#64) s
  | .p2660, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p2664, s => put 31 ((r (.GPR 31#5) s) + (16#64)) s
  | .p2668, s => w .PC (base + 2684#64) s
  | .p2672, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p2676, s => put 31 ((r (.GPR 31#5) s) + (16#64)) s
  | .p2680, s => w .PC (base + 3536#64) s
  | .p2684, s => w .PC (if r (.GPR 3#5) s = 0#64 then base + 4492#64 else base + 2688#64) s
  | .p2688, s => Udivti3.compare (r (.GPR 3#5) s) (r (.GPR 9#5) s) s
  | .p2692, s => put 10 (r (.GPR 9#5) s) s
  | .p2696, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 3524#64 else base + 2700#64) s
  | .p2700, s => w .PC (base + 4492#64) s
  | .p3480, s => Udivti3.compare (0#64) (r (.GPR 10#5) s) s
  | .p3484, s => w .PC (if r (.FLAG .C) s ≠ 1#1 then base + 3496#64 else base + 3488#64) s
  | .p3488, s => put 10 (0#64) s
  | .p3492, s => w .PC (base + 3500#64) s
  | .p3496, s => put 10 (1#64) s
  | .p3500, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 3536#64 else base + 3504#64) s
  | .p3504, s => w .PC (if r (.GPR 3#5) s = 0#64 then base + 4492#64 else base + 3508#64) s
  | .p3508, s => w .PC (if r (.GPR 9#5) s = 0#64 then base + 3576#64 else base + 3512#64) s
  | .p3512, s => put 10 (read_mem_bytes 8 (r (.GPR 8#5) s) s) s
  | .p3516, s => Udivti3.compare (r (.GPR 3#5) s) (r (.GPR 10#5) s) s
  | .p3520, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 4492#64 else base + 3524#64) s
  | .p3524, s => Udivti3.compare (r (.GPR 3#5) s) (r (.GPR 10#5) s) s
  | .p3528, s => w .PC (if r (.FLAG .C) s ≠ 1#1 ∨ r (.FLAG .Z) s = 1#1 then base + 4492#64 else base + 3532#64) s
  | .p3532, s => w .PC (base + 3576#64) s
  | .p3536, s => put 31 ((r (.GPR 31#5) s) - (16#64)) s
  | .p3540, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p3544, s => put 9 ((((r (.GPR 10#5) s).setWidth 32) &&& 1#32).setWidth 64) s
  | .p3548, s => w .PC (if (r (.GPR 9#5) s).setWidth 32 = 0#32 then base + 3564#64 else base + 3552#64) s
  | .p3552, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p3556, s => put 31 ((r (.GPR 31#5) s) + (16#64)) s
  | .p3560, s => w .PC (base + 3576#64) s
  | .p3564, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p3568, s => put 31 ((r (.GPR 31#5) s) + (16#64)) s
  | .p3572, s => w .PC (base + 4492#64) s

theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (he : read_err s = .None) (ha : CheckSPAlignment s) : stepi s = op.effect base s := by
  have hm : op.row ∈ program := by cases op <;> decide
  have hf := hc op.row hm
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  cases op
  all_goals
    simp only [Op.row] at hp hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    change r .PC s = _ at hp
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, Udivti3.compare, Udivti3.next, Vector.widthLoaded,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, ha, hp, BitVec.add_assoc, apply_ite, uint_lsl3_mask,
       uint_and_ones, BoolCodec.pair_read_low, BoolCodec.pair_read_high, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc]

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next,
    Vector.widthLoaded, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next,
    Vector.widthLoaded, state_simp_rules]

theorem Op.aligned (op : Op) (base : BitVec 64) (s : ArmState)
    (ha : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next,
    Vector.widthLoaded, state_simp_rules, ha]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s ha)
    | exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s ha)

def block (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect base s)

theorem block_run (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : Follows base ops s) : run ops.length s = block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block base ops (op.effect base s)
    rw [run, step s base op hc hf.1 he ha]
    exact ih _ (by simpa only [CodeAt, Op.program] using hc)
      (by simpa only [Op.error] using he) (op.aligned base s ha) hf.2

macro "bounded_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    [block, Follows, Op.row, Op.effect, put, next, Vector.widthLoaded,
     Udivti3.compare, Udivti3.next, state_simp_rules, BitVec.add_assoc])

theorem readonly_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hs : ∀ op ∈ ops, op ∉ [.p728, .p732, .p756, .p2644, .p2648,
      .p2664, .p2676, .p3536, .p3540, .p3556, .p3568]) :
    WidthFrame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact WidthFrame.refl s
  | cons op ops ih =>
    have hx := hs op (List.mem_cons_self)
    have hf : WidthFrame s (op.effect base s) := by
      cases op <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false,
        not_true_eq_false, true_or, or_true]
      all_goals
        constructor
        · simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, Vector.widthLoaded, state_simp_rules]
        · simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, Vector.widthLoaded, state_simp_rules]
        · intro reg hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp (disch := simp_all) [Op.effect, put, next, Udivti3.compare,
            Udivti3.next, Vector.widthLoaded, state_simp_rules]
        · intro reg
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, Vector.widthLoaded, state_simp_rules]
        · intro a ha
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, Vector.widthLoaded, state_simp_rules]
    exact hf.trans (ih _ (fun op hop => hs op (List.mem_cons_of_mem _ hop)))

end SszArm.ByteView.Bounded
