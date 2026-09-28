import SszArm.BitVectorContract

namespace SszArm.BitVector.Entry

open BitVector

inductive Op where
  | load | data | size | out | result | divisor | arena | temporary | pointer | payload
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .load => (428, 0xa940d835#32)
  | .data => (432, 0xaa0203f8#32)
  | .size => (436, 0xaa0303f4#32)
  | .out => (440, 0xaa0003f7#32)
  | .result => (444, 0x910243e0#32)
  | .divisor => (448, 0x52800103#32)
  | .arena => (452, 0xaa1303e4#32)
  | .temporary => (456, 0x910243fb#32)
  | .pointer => (460, 0xaa1503e1#32)
  | .payload => (464, 0xaa1603e2#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect : Op → ArmState → ArmState
  | .load, s => next (w (.GPR 22#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s)
      (w (.GPR 21#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s) s))
  | .data, s => put 24 (r (.GPR 2#5) s) s
  | .size, s => put 20 (r (.GPR 3#5) s) s
  | .out, s => put 23 (r (.GPR 0#5) s) s
  | .result, s => put 0 (r (.GPR 31#5) s + 144#64) s
  | .divisor, s => put 3 8#64 s
  | .arena, s => put 4 (r (.GPR 19#5) s) s
  | .temporary, s => put 27 (r (.GPR 31#5) s + 144#64) s
  | .pointer, s => put 1 (r (.GPR 21#5) s) s
  | .payload, s => put 2 (r (.GPR 22#5) s) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched := code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, pc, aligned, BitVec.add_assoc]
  all_goals first | rfl | exact w_of_w_commute (by decide)

structure Stable (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  memory : t.mem = s.mem

theorem Op.stable (op : Op) (s : ArmState) : Stable s (op.effect s) := by
  cases op <;> constructor <;>
    simp (config := {decide := true}) [Op.effect, put, next, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect s)

theorem block_run (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error aligned follows.1]
    have stable := op.stable s
    exact induction _ (by simpa only [CodeAt, stable.program] using code)
      (stable.error.trans error)
      (by simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, stable.sp] using aligned)
      follows.2

def ops : List Op := [.load, .data, .size, .out, .result, .divisor, .arena,
  .temporary, .pointer, .payload]

/-- One compact physical state summary for all ten pre-call instructions. -/
@[irreducible] def result (s : ArmState) (base : BitVec 64) : ArmState :=
  let pointer := read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s
  let payload := read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s
  let temporary := r (.GPR 31#5) s + 144#64
  w .PC (base + 468#64)
    (w (.GPR 2#5) payload (w (.GPR 1#5) pointer
    (w (.GPR 27#5) temporary (w (.GPR 4#5) (r (.GPR 19#5) s)
    (w (.GPR 3#5) 8#64 (w (.GPR 0#5) temporary
    (w (.GPR 23#5) (r (.GPR 0#5) s) (w (.GPR 20#5) (r (.GPR 3#5) s)
    (w (.GPR 24#5) (r (.GPR 2#5) s) (w (.GPR 22#5) payload
    (w (.GPR 21#5) pointer s)))))))))))

/-- Actual entry428 execution; no descriptor/helper values are assumed in
internal registers. They are loaded and moved from the physical entry ABI. -/
theorem runs (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 428#64) : run 10 s = result s base := by
  have follows : Follows base ops s := by
    change r .PC s = _ at pc
    simp (config := {decide := true}) [ops, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, pc, BitVec.add_assoc]
  have executed := block_run ops s base code error aligned follows
  change run 10 s = block ops s at executed
  rw [executed]
  change r .PC s = _ at pc
  simp (config := {decide := true}) [block, ops, Op.effect, put, next, result,
    state_simp_rules, pc, BitVec.add_assoc]
  simp only [w, write_base_pc, write_base_gpr]

end SszArm.BitVector.Entry
