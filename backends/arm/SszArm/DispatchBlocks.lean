import SszArm.DispatchImpl

namespace SszArm.Dispatch.Block

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44 | p48
  | p128 | p132 | p136 | p140 | p144 | p228 | p232 | p412 | p416 | p420 | p424
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd105c3ff#32)
  | .p4 => (4, 0xa9117bfd#32)
  | .p8 => (8, 0xa9126ffc#32)
  | .p12 => (12, 0xa91367fa#32)
  | .p16 => (16, 0xa9145ff8#32)
  | .p20 => (20, 0xa91557f6#32)
  | .p24 => (24, 0xa9164ff4#32)
  | .p28 => (28, 0xf9400028#32)
  | .p32 => (32, 0xaa0403f3#32)
  | .p36 => (36, 0xf100151f#32)
  | .p40 => (40, 0x540002cd#32)
  | .p44 => (44, 0xf100211f#32)
  | .p48 => (48, 0x540005ad#32)
  | .p128 => (128, 0xf100091f#32)
  | .p132 => (132, 0x540008cc#32)
  | .p136 => (136, 0xb4000ea8#32)
  | .p140 => (140, 0xf100051f#32)
  | .p144 => (144, 0x54003921#32)
  | .p228 => (228, 0xf100191f#32)
  | .p232 => (232, 0x54000a60#32)
  | .p412 => (412, 0xf1000d1f#32)
  | .p416 => (416, 0x54000880#32)
  | .p420 => (420, 0xf100111f#32)
  | .p424 => (424, 0x540032e1#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def save (first second : BitVec 5) (offset : BitVec 64) (s : ArmState) : ArmState :=
  next (write_mem_bytes 16 (r (.GPR 31#5) s + offset)
    (r (.GPR second) s ++ r (.GPR first) s) s)

def greater (s : ArmState) : Prop := r (.FLAG .N) s = r (.FLAG .V) s ∧ r (.FLAG .Z) s = 0#1
instance (s : ArmState) : Decidable (greater s) := inferInstanceAs (Decidable (_ ∧ _))

def branch (condition : Prop) [Decidable condition] (offset : BitVec 64) (s : ArmState) : ArmState :=
  w .PC (read_pc s + if condition then offset else 4#64) s

def Op.effect : Op → ArmState → ArmState
  | .p0, s => put 31 (r (.GPR 31#5) s - 368#64) s
  | .p4, s => save 29 30 272#64 s
  | .p8, s => save 28 27 288#64 s
  | .p12, s => save 26 25 304#64 s
  | .p16, s => save 24 23 320#64 s
  | .p20, s => save 22 21 336#64 s
  | .p24, s => save 20 19 352#64 s
  | .p28, s => put 8 (read_mem_bytes 8 (r (.GPR 1#5) s) s) s
  | .p32, s => put 19 (r (.GPR 4#5) s) s
  | .p36, s => Udivti3.compare (r (.GPR 8#5) s) 5#64 s
  | .p40, s => branch (¬ greater s) 88#64 s
  | .p44, s => Udivti3.compare (r (.GPR 8#5) s) 8#64 s
  | .p48, s => branch (¬ greater s) 180#64 s
  | .p128, s => Udivti3.compare (r (.GPR 8#5) s) 2#64 s
  | .p132, s => branch (greater s) 280#64 s
  | .p136, s => branch (r (.GPR 8#5) s = 0#64) 468#64 s
  | .p140, s => Udivti3.compare (r (.GPR 8#5) s) 1#64 s
  | .p144, s => branch (r (.FLAG .Z) s ≠ 1#1) 1828#64 s
  | .p228, s => Udivti3.compare (r (.GPR 8#5) s) 6#64 s
  | .p232, s => branch (r (.FLAG .Z) s = 1#1) 332#64 s
  | .p412, s => Udivti3.compare (r (.GPR 8#5) s) 3#64 s
  | .p416, s => branch (r (.FLAG .Z) s = 1#1) 272#64 s
  | .p420, s => Udivti3.compare (r (.GPR 8#5) s) 4#64 s
  | .p424, s => branch (r (.FLAG .Z) s ≠ 1#1) 1628#64 s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched := code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, save, branch, greater, Udivti3.compare, Udivti3.next,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       aligned, BitVec.sub_eq_add_neg, apply_ite]
  case p28 => exact w_of_w_commute (by decide)
  case p40 | p48 =>
    by_cases n : r (.FLAG .N) s = r (.FLAG .V) s <;>
      by_cases z : r (.FLAG .Z) s = 0#1 <;> simp_all
  all_goals split <;> simp_all

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, save, branch, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, save, branch, Udivti3.compare, Udivti3.next, state_simp_rules]

def effect (ops : List Op) (s : ArmState) : ArmState := ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => CheckSPAlignment s ∧
      read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = effect ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    change run (ops.length + 1) s = effect ops (op.effect s)
    rw [run, step op s base code error follows.1 follows.2.1]
    exact induction _ (by simpa only [CodeAt, Op.program] using code)
      ((op.error s).trans error) follows.2.2

end SszArm.Dispatch.Block
