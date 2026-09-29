import SszArm.HashCombineCalls
import SszArm.Udivti3Arithmetic

namespace SszArm.Hash.Combine

inductive Side where
  | left | right
  deriving DecidableEq

def Side.count : Side → BitVec 5
  | .left => 22
  | .right => 20

def Side.cursor : Side → BitVec 5
  | .left => 23
  | .right => 21

def Side.start : Side → Nat
  | .left => 132
  | .right => 316

def Side.stop : Side → Nat
  | .left => 160
  | .right => 344

def Side.site : Side → CompressSite
  | .left => .left
  | .right => .right

def Side.setup : Side → List Op
  | .left => [.p132, .p136]
  | .right => [.p316, .p320]

def Side.advance : Side → List Op
  | .left => [.p144, .p148, .p152, .p156]
  | .right => [.p328, .p332, .p336, .p340]

@[irreducible] def setup (side : Side) (s : ArmState) : ArmState := block side.setup s

@[irreducible] def advance (side : Side) (s : ArmState) : ArmState := block side.advance s

theorem setup_run (side : Side) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 side.start) :
    run 2 s = setup side s := by
  have follows : Follows base side.setup s := by
    change r .PC s = _ at pc
    cases side <;>
      simp [Follows, Side.setup, Side.start, Op.row, Op.effect, put, next,
        state_simp_rules, aligned, pc, BitVec.add_assoc]
  have execution := runs side.setup s base code error follows
  cases side <;> simpa only [Side.setup, List.length_cons, List.length_nil, setup] using execution

@[simp] theorem setup_program (side : Side) (s : ArmState) :
    (setup side s).program = s.program := by
  simp only [setup, block_program]

@[simp] theorem setup_error (side : Side) (s : ArmState) :
    read_err (setup side s) = read_err s := by
  simp only [setup, block_error]

@[simp] theorem setup_pc (side : Side) (s : ArmState) :
    read_pc (setup side s) = read_pc s + 8#64 := by
  cases side <;> simp [setup, Side.setup, block, Op.effect, put, next,
    state_simp_rules, BitVec.add_assoc]

@[simp] theorem setup_state (side : Side) (s : ArmState) :
    r (.GPR 0#5) (setup side s) = r (.GPR 24#5) s + 64#64 := by
  cases side <;> simp [setup, Side.setup, block, Op.effect, put, next, state_simp_rules]

@[simp] theorem setup_input (side : Side) (s : ArmState) :
    r (.GPR 1#5) (setup side s) = r (.GPR side.cursor) s := by
  cases side <;> simp [setup, Side.setup, Side.cursor, block, Op.effect, put, next, state_simp_rules]

@[simp] theorem setup_register (side : Side) (s : ArmState) (reg : BitVec 5)
    (notZero : reg ≠ 0#5) (notOne : reg ≠ 1#5) :
    r (.GPR reg) (setup side s) = r (.GPR reg) s := by
  cases side <;> simp [setup, Side.setup, block, Op.effect, put, next,
    state_simp_rules, notZero, notOne]

@[simp] theorem setup_vector (side : Side) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (setup side s) = r (.SFP reg) s := by
  cases side <;> simp [setup, Side.setup, block, Op.effect, put, next, state_simp_rules]

@[simp] theorem setup_memory (side : Side) (s : ArmState) :
    (setup side s).mem = s.mem := by
  cases side <;> simp [setup, Side.setup, block, Op.effect, put, next, state_simp_rules]

theorem setup_aligned (side : Side) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (setup side s) := by
  cases side <;> simpa [setup, Side.setup, block, Op.effect, put, next,
    state_simp_rules] using aligned

theorem setup_call_pc (side : Side) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 side.start) :
    read_pc (setup side s) = base + BitVec.ofNat 64 side.site.op.row.1 := by
  rw [setup_pc, pc]
  cases side <;> simp [Side.start, Side.site, CompressSite.op, Op.row, BitVec.add_assoc]

theorem advance_run (side : Side) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (side.start + 12)) :
    run 4 s = advance side s := by
  have follows : Follows base side.advance s := by
    change r .PC s = _ at pc
    cases side <;>
      simp [Follows, Side.advance, Side.start, Op.row, Op.effect, put, next, compare,
        state_simp_rules, aligned, pc, BitVec.add_assoc]
  have execution := runs side.advance s base code error follows
  cases side <;> simpa only [Side.advance, List.length_cons, List.length_nil, advance] using execution

@[simp] theorem advance_program (side : Side) (s : ArmState) :
    (advance side s).program = s.program := by simp only [advance, block_program]

@[simp] theorem advance_error (side : Side) (s : ArmState) :
    read_err (advance side s) = read_err s := by simp only [advance, block_error]

@[simp] theorem advance_count (side : Side) (s : ArmState) :
    r (.GPR side.count) (advance side s) = r (.GPR side.count) s - 64#64 := by
  cases side <;> simp [advance, Side.advance, Side.count, block, Op.effect, put, next,
    compare, branch, state_simp_rules]

@[simp] theorem advance_cursor (side : Side) (s : ArmState) :
    r (.GPR side.cursor) (advance side s) = r (.GPR side.cursor) s + 64#64 := by
  cases side <;> simp [advance, Side.advance, Side.cursor, block, Op.effect, put, next,
    compare, branch, state_simp_rules]

@[simp] theorem advance_register (side : Side) (s : ArmState) (reg : BitVec 5)
    (notCount : reg ≠ side.count) (notCursor : reg ≠ side.cursor) :
    r (.GPR reg) (advance side s) = r (.GPR reg) s := by
  cases side <;> simp_all [advance, Side.advance, Side.count, Side.cursor, block, Op.effect,
    put, next, compare, branch, state_simp_rules]

@[simp] theorem advance_vector (side : Side) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (advance side s) = r (.SFP reg) s := by
  cases side <;> simp [advance, Side.advance, block, Op.effect, put, next,
    compare, branch, state_simp_rules]

@[simp] theorem advance_memory (side : Side) (s : ArmState) :
    (advance side s).mem = s.mem := by
  cases side <;> simp [advance, Side.advance, block, Op.effect, put, next,
    compare, branch, state_simp_rules]

theorem advance_aligned (side : Side) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (advance side s) := by
  cases side <;> simpa [advance, Side.advance, block, Op.effect, put, next,
    compare, branch, state_simp_rules] using aligned

private theorem higher63 (x : BitVec 64) :
    ((AddWithCarry x 18446744073709551552#64 1#1).2.c = 1#1 ∧
      (AddWithCarry x 18446744073709551552#64 1#1).2.z = 0#1) ↔ 64 ≤ x.toNat := by
  have complement : ~~~63#64 = 18446744073709551552#64 := by decide
  have carry := Udivti3.cmp_carry x 63#64
  have nonzero := Udivti3.cmp_nonzero x 63#64
  rw [complement] at carry nonzero
  rw [carry, nonzero]
  bv_omega

theorem advance_pc (side : Side) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 (side.start + 12)) :
    read_pc (advance side s) =
      if 64 ≤ (r (.GPR side.count) s - 64#64).toNat
      then base + BitVec.ofNat 64 side.start else base + BitVec.ofNat 64 side.stop := by
  change r .PC s = _ at pc
  cases side <;>
    simp (config := {decide := true, instances := true})
      [advance, Side.advance, Side.count, Side.start, Side.stop, block, Op.effect,
        put, next, compare, branch, state_simp_rules, pc, BitVec.add_assoc,
        higher63]

end SszArm.Hash.Combine
