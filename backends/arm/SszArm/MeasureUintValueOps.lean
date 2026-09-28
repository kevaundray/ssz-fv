import SszArm.MeasureContract
import SszArm.EmitDispatchOps
import SszArm.NatToU128Memory

namespace SszArm.Measure.Uint

open UintCodec

abbrev next := Emit.Dispatch.next
abbrev compare64 := Emit.Dispatch.compare64
abbrev compare32 := Emit.Dispatch.compare32

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

inductive ValueOp where
  | p348 | p352 | p356 | p360 | p364 | p368 | p372 | p376 | p380
  | p384 | p388 | p392 | p396 | p400 | p404 | p408 | p412 | p2732
  deriving DecidableEq

def ValueOp.row : ValueOp → Nat × BitVec 32
  | .p348 => (348, 0x7100051f#32)
  | .p352 => (352, 0x54006fa1#32)
  | .p356 => (356, 0xa940a2a9#32)
  | .p360 => (360, 0xb4003949#32)
  | .p364 => (364, 0xd1002129#32)
  | .p368 => (368, 0xb40049e8#32)
  | .p372 => (372, 0xd10043ff#32)
  | .p376 => (376, 0xf90003ea#32)
  | .p380 => (380, 0xaa0803ea#32)
  | .p384 => (384, 0xd37df14a#32)
  | .p388 => (388, 0x8b0a012a#32)
  | .p392 => (392, 0xf940014b#32)
  | .p396 => (396, 0xf94003ea#32)
  | .p400 => (400, 0x910043ff#32)
  | .p404 => (404, 0xaa0803ea#32)
  | .p408 => (408, 0xd1000508#32)
  | .p412 => (412, 0xb4fffeab#32)
  | .p2732 => (2732, 0xaa1f03e9#32)

def ValueOp.effect (base : BitVec 64) : ValueOp → ArmState → ArmState
  | .p348, s => compare32 ((r (.GPR 8#5) s).setWidth 32) 1#32 s
  | .p352, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 356#64 else base + 3924#64) s
  | .p356, s => w (.GPR 8#5) (read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) s)
      (put 9 (read_mem_bytes 8 (r (.GPR 21#5) s + 8#64) s) s)
  | .p360, s => w .PC (if r (.GPR 9#5) s = 0#64 then base + 2192#64 else base + 364#64) s
  | .p364, s => put 9 (r (.GPR 9#5) s - 8#64) s
  | .p368, s => w .PC (if r (.GPR 8#5) s = 0#64 then base + 2732#64 else base + 372#64) s
  | .p372, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p376, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p380, s => put 10 (r (.GPR 8#5) s) s
  | .p384, s => put 10 (r (.GPR 10#5) s <<< 3) s
  | .p388, s => put 10 (r (.GPR 9#5) s + r (.GPR 10#5) s) s
  | .p392, s => put 11 (read_mem_bytes 8 (r (.GPR 10#5) s) s) s
  | .p396, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p400, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p404, s => put 10 (r (.GPR 8#5) s) s
  | .p408, s => put 8 (r (.GPR 8#5) s - 1#64) s
  | .p412, s => w .PC (if r (.GPR 11#5) s = 0#64 then base + 368#64 else base + 416#64) s
  | .p2732, s => put 9 0#64 s

theorem value_step (s : ArmState) (base : BitVec 64) (op : ValueOp)
    (code : CodeAt s base) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) :
    stepi s = op.effect base s := by
  have member : op.row ∈ bodyProgram := by
    cases op <;> unfold bodyProgram
    case p400 | p404 | p408 | p412 =>
      iterate 9 apply List.mem_append_left
      apply List.mem_append_right
      decide
    case p2732 =>
      iterate 4 apply List.mem_append_left
      apply List.mem_append_right
      decide
    all_goals
      iterate 10 apply List.mem_append_left
      decide
  have fetched := body_codeAt code op.row member
  cases op
  all_goals
    simp only [ValueOp.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [ValueOp.effect, put, next, compare32, Emit.Dispatch.next,
       Emit.Dispatch.compare32, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
       aligned, pc, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.sub_eq_add_neg,
       uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]

@[simp] theorem ValueOp.program (op : ValueOp) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [ValueOp.effect, put, next, compare32, Emit.Dispatch.compare32,
    Emit.Dispatch.next, state_simp_rules]

@[simp] theorem ValueOp.error (op : ValueOp) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [ValueOp.effect, put, next, compare32, Emit.Dispatch.compare32,
    Emit.Dispatch.next, state_simp_rules]

theorem ValueOp.aligned (op : ValueOp) (base : BitVec 64) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  cases op <;> simp [ValueOp.effect, put, next, compare32, Emit.Dispatch.compare32,
    Emit.Dispatch.next, state_simp_rules, aligned]
  · exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  · exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)

@[simp] theorem ValueOp.vector (op : ValueOp) (base : BitVec 64) (s : ArmState)
    (reg : BitVec 5) : r (.SFP reg) (op.effect base s) = r (.SFP reg) s := by
  cases op <;> simp [ValueOp.effect, put, next, compare32, Emit.Dispatch.compare32,
    Emit.Dispatch.next, state_simp_rules]

def valueBlock (base : BitVec 64) (ops : List ValueOp) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def ValueFollows (base : BitVec 64) : List ValueOp → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      ValueFollows base ops (op.effect base s)

theorem value_run (base : BitVec 64) (ops : List ValueOp) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (follows : ValueFollows base ops s) : run ops.length s = valueBlock base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = valueBlock base ops (op.effect base s)
    rw [run, value_step s base op code follows.1 error aligned]
    exact ih _ (code.congr (op.program base s))
      ((op.error base s).trans error) (op.aligned base s aligned) follows.2

end SszArm.Measure.Uint
