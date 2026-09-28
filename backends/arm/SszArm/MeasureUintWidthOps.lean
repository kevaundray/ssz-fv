import SszArm.MeasureUintValueOps

namespace SszArm.Measure.Uint

open UintCodec

inductive WidthOp where
  | p2736 | p2740 | p2744 | p2748 | p2752 | p2756 | p2760 | p2764 | p2768
  | p2772 | p2776 | p2780 | p2784 | p2788 | p2792 | p2796 | p2800 | p2804
  | p2808 | p2812 | p2816 | p2820 | p2824 | p2876 | p2880 | p2884 | p2888
  | p2892 | p2896 | p3012 | p3016 | p3904 | p3908 | p3912 | p3916 | p3920
  deriving DecidableEq

def WidthOp.row : WidthOp → Nat × BitVec 32
  | .p2736 => (2736, 0xa940d035#32)
  | .p2740 => (2740, 0xb4000275#32)
  | .p2744 => (2744, 0xd100068b#32)
  | .p2748 => (2748, 0xb100057f#32)
  | .p2752 => (2752, 0x540003e0#32)
  | .p2756 => (2756, 0xd10043ff#32)
  | .p2760 => (2760, 0xf90003e9#32)
  | .p2764 => (2764, 0xaa0b03e9#32)
  | .p2768 => (2768, 0xd37df129#32)
  | .p2772 => (2772, 0x8b0902a9#32)
  | .p2776 => (2776, 0xf940012c#32)
  | .p2780 => (2780, 0xf94003e9#32)
  | .p2784 => (2784, 0x910043ff#32)
  | .p2788 => (2788, 0xaa0b03ea#32)
  | .p2792 => (2792, 0xd100056b#32)
  | .p2796 => (2796, 0xb4fffe8c#32)
  | .p2800 => (2800, 0x9100054a#32)
  | .p2804 => (2804, 0xf1000d5f#32)
  | .p2808 => (2808, 0x540029c2#32)
  | .p2812 => (2812, 0x14000011#32)
  | .p2816 => (2816, 0xaa1f03eb#32)
  | .p2820 => (2820, 0xaa1403ea#32)
  | .p2824 => (2824, 0x14000110#32)
  | .p2876 => (2876, 0xb4002034#32)
  | .p2880 => (2880, 0xf94002aa#32)
  | .p2884 => (2884, 0xf1000a9f#32)
  | .p2888 => (2888, 0x540003e3#32)
  | .p2892 => (2892, 0xf94006ab#32)
  | .p2896 => (2896, 0x140000fe#32)
  | .p3012 => (3012, 0xaa1f03eb#32)
  | .p3016 => (3016, 0x140000e0#32)
  | .p3904 => (3904, 0xaa1f03eb#32)
  | .p3908 => (3908, 0xaa1f03ea#32)
  | .p3912 => (3912, 0xeb08015f#32)
  | .p3916 => (3916, 0xfa09017f#32)
  | .p3920 => (3920, 0x54000702#32)

def WidthOp.effect (base : BitVec 64) : WidthOp → ArmState → ArmState
  | .p2736, s => w (.GPR 20#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s)
      (put 21 (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s) s)
  | .p2740, s => w .PC (if r (.GPR 21#5) s = 0#64 then base + 2816#64 else base + 2744#64) s
  | .p2744, s => put 11 (r (.GPR 20#5) s - 1#64) s
  | .p2748, s => write_pstate (AddWithCarry (r (.GPR 11#5) s) 1#64 0#1).2 (next s)
  | .p2752, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 2876#64 else base + 2756#64) s
  | .p2756, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p2760, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p2764, s => put 9 (r (.GPR 11#5) s) s
  | .p2768, s => put 9 (r (.GPR 9#5) s <<< 3) s
  | .p2772, s => put 9 (r (.GPR 21#5) s + r (.GPR 9#5) s) s
  | .p2776, s => put 12 (read_mem_bytes 8 (r (.GPR 9#5) s) s) s
  | .p2780, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p2784, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p2788, s => put 10 (r (.GPR 11#5) s) s
  | .p2792, s => put 11 (r (.GPR 11#5) s - 1#64) s
  | .p2796, s => w .PC (if r (.GPR 12#5) s = 0#64 then base + 2748#64 else base + 2800#64) s
  | .p2800, s => put 10 (r (.GPR 10#5) s + 1#64) s
  | .p2804, s => compare64 (r (.GPR 10#5) s) 3#64 s
  | .p2808, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 4144#64 else base + 2812#64) s
  | .p2812, s => w .PC (base + 2880#64) s
  | .p2816, s => put 11 0#64 s
  | .p2820, s => put 10 (r (.GPR 20#5) s) s
  | .p2824, s => w .PC (base + 3912#64) s
  | .p2876, s => w .PC (if r (.GPR 20#5) s = 0#64 then base + 3904#64 else base + 2880#64) s
  | .p2880, s => put 10 (read_mem_bytes 8 (r (.GPR 21#5) s) s) s
  | .p2884, s => compare64 (r (.GPR 20#5) s) 2#64 s
  | .p2888, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 2892#64 else base + 3012#64) s
  | .p2892, s => put 11 (read_mem_bytes 8 (r (.GPR 21#5) s + 8#64) s) s
  | .p2896, s => w .PC (base + 3912#64) s
  | .p3012, s => put 11 0#64 s
  | .p3016, s => w .PC (base + 3912#64) s
  | .p3904, s => put 11 0#64 s
  | .p3908, s => put 10 0#64 s
  | .p3912, s => compare64 (r (.GPR 10#5) s) (r (.GPR 8#5) s) s
  | .p3916, s => write_pstate
      (AddWithCarry (r (.GPR 11#5) s) (~~~r (.GPR 9#5) s) (r (.FLAG .C) s)).2 (next s)
  | .p3920, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 4144#64 else base + 3924#64) s

theorem width_step (s : ArmState) (base : BitVec 64) (op : WidthOp)
    (code : CodeAt s base) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) :
    stepi s = op.effect base s := by
  have member : op.row ∈ bodyProgram := by
    cases op <;> unfold bodyProgram
    case p2876 | p2880 | p2884 | p2888 | p2892 | p2896 | p3012 | p3016 =>
      iterate 3 apply List.mem_append_left
      apply List.mem_append_right
      decide
    case p3904 | p3908 | p3912 | p3916 | p3920 =>
      apply List.mem_append_left
      apply List.mem_append_right
      decide
    all_goals
      iterate 4 apply List.mem_append_left
      apply List.mem_append_right
      decide
  have fetched := body_codeAt code op.row member
  cases op
  all_goals
    simp only [WidthOp.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [WidthOp.effect, put, next, compare64, Emit.Dispatch.next, Emit.Dispatch.compare64,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc,
       BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]

@[simp] theorem WidthOp.program (op : WidthOp) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [WidthOp.effect, put, next, compare64, Emit.Dispatch.compare64,
    Emit.Dispatch.next, state_simp_rules]

@[simp] theorem WidthOp.error (op : WidthOp) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [WidthOp.effect, put, next, compare64, Emit.Dispatch.compare64,
    Emit.Dispatch.next, state_simp_rules]

theorem WidthOp.aligned (op : WidthOp) (base : BitVec 64) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  cases op <;> simp [WidthOp.effect, put, next, compare64, Emit.Dispatch.compare64,
    Emit.Dispatch.next, state_simp_rules, aligned]
  · exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  · exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)

@[simp] theorem WidthOp.vector (op : WidthOp) (base : BitVec 64) (s : ArmState)
    (reg : BitVec 5) : r (.SFP reg) (op.effect base s) = r (.SFP reg) s := by
  cases op <;> simp [WidthOp.effect, put, next, compare64, Emit.Dispatch.compare64,
    Emit.Dispatch.next, state_simp_rules]

def widthBlock (base : BitVec 64) (ops : List WidthOp) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def WidthFollows (base : BitVec 64) : List WidthOp → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      WidthFollows base ops (op.effect base s)

theorem width_run (base : BitVec 64) (ops : List WidthOp) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (follows : WidthFollows base ops s) : run ops.length s = widthBlock base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = widthBlock base ops (op.effect base s)
    rw [run, width_step s base op code follows.1 error aligned]
    exact ih _ (code.congr (op.program base s))
      ((op.error base s).trans error) (op.aligned base s aligned) follows.2

end SszArm.Measure.Uint
