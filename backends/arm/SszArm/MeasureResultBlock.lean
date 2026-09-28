import SszArm.MeasureContract
import SszArm.BoolAlignment
import SszArm.NatExactState
import SszArm.BitVectorProgram

namespace SszArm.Measure.Result

/-- One original instruction, with its decoder and linked-image witnesses. -/
structure Op where
  offset : Nat
  word : BitVec 32
  instruction : ArmInst
  decoded : decode_raw_inst word = some instruction
  member : (offset, word) ∈ bodyProgram

def Op.effect (op : Op) (s : ArmState) : ArmState := exec_inst op.instruction s

theorem Op.step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 op.offset) : stepi s = op.effect s := by
  exact stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans (code.body (op.offset, op.word) op.member)) op.decoded

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program :=
  SszArm.BitVector.exec_program op.instruction s

def effect (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun state op => op.effect state) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_err s = .None ∧
      read_pc s = base + BitVec.ofNat 64 op.offset ∧ Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (follows : Follows base ops s) : run ops.length s = effect ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    change run (ops.length + 1) s = effect ops (op.effect s)
    rw [run, op.step s base code follows.1 follows.2.1]
    exact induction _ (code.congr (op.program s)) follows.2.2

end SszArm.Measure.Result
