import SszArm.CodecLinkedNatCmpUsize
import SszArm.NatToU128Memory

namespace SszArm.Codec.Decode.NatCmpUsize

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44 | p48
  | p52 | p56 | p60 | p64 | p68 | p72 | p76 | p80 | p84 | p88 | p92 | p96
  | p100 | p104 | p108 | p112 | p116 | p120 | p124 | p128 | p132 | p136
  | p140 | p144 | p148 | p152 | p156 | p160 | p164 | p168
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xb4000340#32)
  | .p4 => (4, 0xd1000429#32)
  | .p8 => (8, 0xb100053f#32)
  | .p12 => (12, 0x54000220#32)
  | .p16 => (16, 0xd10043ff#32)
  | .p20 => (20, 0xf90003eb#32)
  | .p24 => (24, 0xaa0903eb#32)
  | .p28 => (28, 0xd37df16b#32)
  | .p32 => (32, 0x8b0b000b#32)
  | .p36 => (36, 0xf940016a#32)
  | .p40 => (40, 0xf94003eb#32)
  | .p44 => (44, 0x910043ff#32)
  | .p48 => (48, 0xaa0903e8#32)
  | .p52 => (52, 0xd1000529#32)
  | .p56 => (56, 0xb4fffe8a#32)
  | .p60 => (60, 0x91000508#32)
  | .p64 => (64, 0xf1000d1f#32)
  | .p68 => (68, 0x54000083#32)
  | .p72 => (72, 0x52800020#32)
  | .p76 => (76, 0xd65f03c0#32)
  | .p80 => (80, 0xb40000c1#32)
  | .p84 => (84, 0xf9400009#32)
  | .p88 => (88, 0xf100083f#32)
  | .p92 => (92, 0x540000a3#32)
  | .p96 => (96, 0xf9400408#32)
  | .p100 => (100, 0x14000004#32)
  | .p104 => (104, 0xaa1f03e8#32)
  | .p108 => (108, 0x14000003#32)
  | .p112 => (112, 0xaa1f03e8#32)
  | .p116 => (116, 0xaa0903e1#32)
  | .p120 => (120, 0xeb01005f#32)
  | .p124 => (124, 0xfa0803ff#32)
  | .p128 => (128, 0x54000063#32)
  | .p132 => (132, 0x52800009#32)
  | .p136 => (136, 0x14000002#32)
  | .p140 => (140, 0x52800029#32)
  | .p144 => (144, 0xeb02003f#32)
  | .p148 => (148, 0xfa1f011f#32)
  | .p152 => (152, 0x54000062#32)
  | .p156 => (156, 0x2a3f03e0#32)
  | .p160 => (160, 0x14000002#32)
  | .p164 => (164, 0x2a0903e0#32)
  | .p168 => (168, 0xd65f03c0#32)

abbrev CodeAt := Linked.NatCmpUsize.CodeAt

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p0, s => w .PC (if r (.GPR 0#5) s = 0#64 then base + 104#64 else base + 4#64) s
  | .p4, s => put 9 (r (.GPR 1#5) s - 1#64) s
  | .p8, s => write_pstate (AddWithCarry (r (.GPR 9#5) s) 1#64 0#1).2 (next s)
  | .p12, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 80#64 else base + 16#64) s
  | .p16, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p20, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 11#5) s) s)
  | .p24, s => put 11 (r (.GPR 9#5) s) s
  | .p28, s => put 11 (r (.GPR 11#5) s <<< 3) s
  | .p32, s => put 11 (r (.GPR 0#5) s + r (.GPR 11#5) s) s
  | .p36, s => put 10 (read_mem_bytes 8 (r (.GPR 11#5) s) s) s
  | .p40, s => put 11 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p44, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p48, s => put 8 (r (.GPR 9#5) s) s
  | .p52, s => put 9 (r (.GPR 9#5) s - 1#64) s
  | .p56, s => w .PC (if r (.GPR 10#5) s = 0#64 then base + 8#64 else base + 60#64) s
  | .p60, s => put 8 (r (.GPR 8#5) s + 1#64) s
  | .p64, s => Udivti3.compare (r (.GPR 8#5) s) 3#64 s
  | .p68, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 72#64 else base + 84#64) s
  | .p72, s => put 0 1#64 s
  | .p76, s => w .PC (r (.GPR 30#5) s) s
  | .p80, s => w .PC (if r (.GPR 1#5) s = 0#64 then base + 104#64 else base + 84#64) s
  | .p84, s => put 9 (read_mem_bytes 8 (r (.GPR 0#5) s) s) s
  | .p88, s => Udivti3.compare (r (.GPR 1#5) s) 2#64 s
  | .p92, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 96#64 else base + 112#64) s
  | .p96, s => put 8 (read_mem_bytes 8 (r (.GPR 0#5) s + 8#64) s) s
  | .p100, s => w .PC (base + 116#64) s
  | .p104, s => put 8 0#64 s
  | .p108, s => w .PC (base + 120#64) s
  | .p112, s => put 8 0#64 s
  | .p116, s => put 1 (r (.GPR 9#5) s) s
  | .p120, s => Udivti3.compare (r (.GPR 2#5) s) (r (.GPR 1#5) s) s
  | .p124, s => write_pstate
      (AddWithCarry 0#64 (~~~r (.GPR 8#5) s) (r (.FLAG .C) s)).2 (next s)
  | .p128, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 132#64 else base + 140#64) s
  | .p132, s => put 9 0#64 s
  | .p136, s => w .PC (base + 144#64) s
  | .p140, s => put 9 1#64 s
  | .p144, s => Udivti3.compare (r (.GPR 1#5) s) (r (.GPR 2#5) s) s
  | .p148, s => write_pstate
      (AddWithCarry (r (.GPR 8#5) s) (~~~0#64) (r (.FLAG .C) s)).2 (next s)
  | .p152, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 164#64 else base + 156#64) s
  | .p156, s => put 0 4294967295#64 s
  | .p160, s => w .PC (base + 168#64) s
  | .p164, s => put 0 (((r (.GPR 9#5) s).setWidth 32).setWidth 64) s
  | .p168, s => w .PC (r (.GPR 30#5) s) s

theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (code : CodeAt s base) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) :
    stepi s = op.effect base s := by
  have fetched := code op.row (by cases op <;> decide)
  have zero : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, aligned, pc, BitVec.add_assoc, apply_ite,
       UintCodec.uint_lsl3_mask, UintCodec.uint_and_ones, zero]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.sfp (op : Op) (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect base s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem Op.aligned (op : Op) (base : BitVec 64) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules, aligned]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
    | exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)

def block (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect base s)

theorem block_run (base : BitVec 64) (ops : List Op) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (follows : Follows base ops s) : run ops.length s = block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block base ops (op.effect base s)
    rw [run, step s base op code follows.1 error aligned]
    exact ih _ (by simpa only [CodeAt, Linked.NatCmpUsize.CodeAt, Linked.WordsAt, Op.program] using code)
      (by simpa only [Op.error] using error) (op.aligned base s aligned) follows.2

end SszArm.Codec.Decode.NatCmpUsize
