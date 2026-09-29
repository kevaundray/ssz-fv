import SszArm.CodecFixedMeasureEntryOps
import SszArm.CodecFixedMeasureReturnOps
import SszArm.CodecFixedMeasureVectorOps
import SszArm.CodecFixedMeasureBitsOps
import SszArm.CodecFixedMeasureFieldsOps

namespace SszArm.Codec.Fixed.MeasureFixed

/-- Disjoint instruction families partition the complete linked measure_fixed
extent. Calls remain real BL instructions, not atomic helper summaries. -/
inductive Op where
  | entry (op : Entry.Op)
  | finish (op : Return.Op)
  | vector (op : Vector.Op)
  | bits (op : Bits.Op)
  | fields (op : Fields.Op)

def Op.row : Op → Nat × BitVec 32
  | .entry op => op.row
  | .finish op => op.row
  | .vector op => op.row
  | .bits op => op.row
  | .fields op => op.row

def Op.effect : Op → ArmState → ArmState
  | .entry op => op.effect
  | .finish op => op.effect
  | .vector op => op.effect
  | .bits op => op.effect
  | .fields op => op.effect

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureFixed.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  cases op with
  | entry op => exact Entry.step op s base code error aligned pc
  | finish op => exact Return.step op s base code error aligned pc
  | vector op => exact Vector.step op s base code error aligned pc
  | bits op => exact Bits.step op s base code error aligned pc
  | fields op => exact Fields.step op s base code error aligned pc

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op with
  | entry op => exact op.program s
  | finish op => exact op.program s
  | vector op => exact op.program s
  | bits op => exact op.program s
  | fields op => exact op.program s

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op with
  | entry op => exact op.error s
  | finish op => exact op.error s
  | vector op => exact op.error s
  | bits op => exact op.error s
  | fields op => exact op.error s

def block (ops : List Op) (s : ArmState) : ArmState := ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => CheckSPAlignment s ∧ read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect s)

theorem block_run (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureFixed.CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1 follows.2.1]
    exact ih _ (by simpa only [Linked.MeasureFixed.CodeAt, Linked.WordsAt, Op.program] using code)
      ((op.error s).trans error) follows.2.2

@[simp] theorem block_program (ops : List Op) (s : ArmState) : (block ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.program s)

@[simp] theorem block_error (ops : List Op) (s : ArmState) : read_err (block ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.error s)

end SszArm.Codec.Fixed.MeasureFixed
