import SszArm.BoolMemory
import SszArm.BoolAlignment
import SszArm.Udivti3Arithmetic

namespace SszArm.Codec.Decode.ReadOffset

/-- The non-panicking path of the linked `read_offset`, including its activation
and return. The four bounds-panic edges are represented by their real targets. -/
inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32
  | p36 | p40 | p44 | p48 | p52 | p56 | p60 | p64 | p68
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd10043ff#32)
  | .p4 => (4, 0xf90003fe#32)
  | .p8 => (8, 0xb4000201#32)
  | .p12 => (12, 0xf100043f#32)
  | .p16 => (16, 0x54000200#32)
  | .p20 => (20, 0xf100083f#32)
  | .p24 => (24, 0x54000209#32)
  | .p28 => (28, 0xf1000c3f#32)
  | .p32 => (32, 0x54000220#32)
  | .p36 => (36, 0x39400008#32)
  | .p40 => (40, 0x39400409#32)
  | .p44 => (44, 0x3940080a#32)
  | .p48 => (48, 0xaa092108#32)
  | .p52 => (52, 0x39400c09#32)
  | .p56 => (56, 0xaa0a4108#32)
  | .p60 => (60, 0xaa096100#32)
  | .p64 => (64, 0xf84107fe#32)
  | .p68 => (68, 0xd65f03c0#32)

def CodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  ∀ op : Op, s.program.find? (base + BitVec.ofNat 64 op.row.1) = some op.row.2

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p0, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p4, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 30#5) s) s)
  | .p8, s => w .PC (if r (.GPR 1#5) s = 0#64 then base + 72#64 else base + 12#64) s
  | .p12, s => Udivti3.compare (r (.GPR 1#5) s) 1#64 s
  | .p16, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 80#64 else base + 20#64) s
  | .p20, s => Udivti3.compare (r (.GPR 1#5) s) 2#64 s
  | .p24, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1
      then base + 28#64 else base + 88#64) s
  | .p28, s => Udivti3.compare (r (.GPR 1#5) s) 3#64 s
  | .p32, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 100#64 else base + 36#64) s
  | .p36, s => put 8 ((read_mem_bytes 1 (r (.GPR 0#5) s) s).setWidth 64) s
  | .p40, s => put 9 ((read_mem_bytes 1 (r (.GPR 0#5) s + 1#64) s).setWidth 64) s
  | .p44, s => put 10 ((read_mem_bytes 1 (r (.GPR 0#5) s + 2#64) s).setWidth 64) s
  | .p48, s => put 8 (r (.GPR 8#5) s ||| (r (.GPR 9#5) s <<< 8)) s
  | .p52, s => put 9 ((read_mem_bytes 1 (r (.GPR 0#5) s + 3#64) s).setWidth 64) s
  | .p56, s => put 8 (r (.GPR 8#5) s ||| (r (.GPR 10#5) s <<< 16)) s
  | .p60, s => put 0 (r (.GPR 8#5) s ||| (r (.GPR 9#5) s <<< 24)) s
  | .p64, s => w (.GPR 31#5) (r (.GPR 31#5) s + 16#64)
      (put 30 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s)
  | .p68, s => w .PC (r (.GPR 30#5) s) s

/-- Every step is LNSym execution of its linked raw word, not a helper oracle. -/
theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (code : CodeAt s base) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) :
    stepi s = op.effect base s := by
  have fetched := code op
  have zero : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have lowerOrSame : (r (.FLAG .C) s ≠ 1#1 ∨ r (.FLAG .Z) s = 1#1) ↔
      ¬(r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1) := by bv_omega
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, aligned, pc, BitVec.add_assoc, apply_ite, zero, lowerOrSame]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]
  all_goals
    by_cases carry : r (.FLAG .C) s = 1#1 <;>
      by_cases zeroFlag : r (.FLAG .Z) s = 0#1 <;> simp_all

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
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
    exact ih _ (by simpa only [CodeAt, Op.program] using code)
      (by simpa only [Op.error] using error) (op.aligned base s aligned) follows.2

end SszArm.Codec.Decode.ReadOffset
