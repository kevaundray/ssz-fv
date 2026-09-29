import SszArm.IndicesLinkedRebase
import SszArm.NatAddReturnValues
import SszArm.IndicesStorage

set_option autoImplicit false

namespace SszArm.Indices.RebaseReturn

open BoolCodec
open NatAdd (put next)

inductive ReturnOp where
  | reserve | save9 | save10 | output | statusAddress | zero32 | zero64
  | storeZero | storeSmall | storeStatus | restore10 | restore9 | release | ret | pair
  deriving DecidableEq

def ReturnOp.word : ReturnOp → BitVec 32
  | .reserve => 0xd10043ff#32 | .save9 => 0xf90003e9#32
  | .save10 => 0xf90007ea#32 | .output => 0x91000009#32
  | .statusAddress => 0x91010129#32 | .zero32 => 0x5280000a#32
  | .zero64 => 0xd280000a#32 | .storeZero => 0xf900012a#32
  | .storeSmall => 0xf9000528#32 | .storeStatus => 0xb900012a#32
  | .restore10 => 0xf94007ea#32 | .restore9 => 0xf94003e9#32
  | .release => 0x910043ff#32 | .ret => 0xd65f03c0#32
  | .pair => 0xa900280b#32

def ReturnOp.effect (op : ReturnOp) (s : ArmState) : ArmState :=
  match op with
  | .reserve => put 31 (r (.GPR 31#5) s - 16#64) s
  | .save9 => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .save10 => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .output => put 9 (r (.GPR 0#5) s) s
  | .statusAddress => put 9 (r (.GPR 9#5) s + 64#64) s
  | .zero32 | .zero64 => put 10 0#64 s
  | .storeZero => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .storeSmall => next (write_mem_bytes 8 (r (.GPR 9#5) s + 8#64) (r (.GPR 8#5) s) s)
  | .storeStatus => next (write_mem_bytes 4 (r (.GPR 9#5) s) ((r (.GPR 10#5) s).setWidth 32) s)
  | .restore10 => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .restore9 => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .release => put 31 (r (.GPR 31#5) s + 16#64) s
  | .ret => w .PC (r (.GPR 30#5) s) s
  | .pair => next (write_mem_bytes 16 (r (.GPR 0#5) s)
      (r (.GPR 10#5) s ++ r (.GPR 11#5) s) s)

theorem ReturnOp.step (op : ReturnOp) (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some op.word) :
    stepi s = op.effect s := by
  cases op <;>
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
      (fetch_inst_from_program.trans fetched) rfl] <;>
    simp (config := {decide := true, instances := true})
      [ReturnOp.effect, put, next, exec_inst, state_simp_rules,
        bitvec_rules, minimal_theory, aligned]
  all_goals first | rfl | exact w_of_w_commute (by decide)

@[simp] theorem ReturnOp.program (op : ReturnOp) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [effect, put, next, state_simp_rules]

@[simp] theorem ReturnOp.error (op : ReturnOp) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [effect, put, next, state_simp_rules]

theorem ReturnOp.aligned (op : ReturnOp) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (op.effect s) := by
  cases op <;> simp [effect, put, next, state_simp_rules, aligned]
  all_goals first
    | exact aligned_sub16 _ (stack_aligned s aligned)
    | exact aligned_add16 _ (stack_aligned s aligned)

def returnBlock (ops : List (Nat × ReturnOp)) (s : ArmState) : ArmState :=
  ops.foldl (fun t row => row.2.effect t) s

def ReturnFollows (base : BitVec 64) : List (Nat × ReturnOp) → ArmState → Prop
  | [], _ => True
  | row :: rest, s => read_pc s = base + BitVec.ofNat 64 row.1 ∧
      ReturnFollows base rest (row.2.effect s)

theorem returnBlock_run (ops : List (Nat × ReturnOp)) (s : ArmState) (base : BitVec 64)
    (code : ∀ row ∈ ops, s.program.find? (base + BitVec.ofNat 64 row.1) = some row.2.word)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (follows : ReturnFollows base ops s) : run ops.length s = returnBlock ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons row rest ih =>
    change run (rest.length + 1) s = returnBlock rest (row.2.effect s)
    rw [run, row.2.step s error aligned
      (by rw [follows.1]; exact code _ List.mem_cons_self)]
    exact ih _ (fun child h => by
      simpa only [ReturnOp.program] using code child (List.mem_cons_of_mem _ h))
      ((ReturnOp.error _ _).trans error) (row.2.aligned s aligned) follows.2

def smallOps : List (Nat × ReturnOp) :=
  [(472, .reserve), (476, .save9), (480, .save10), (484, .output),
   (488, .zero64), (492, .storeZero), (496, .storeSmall),
   (500, .restore10), (504, .restore9), (508, .release), (512, .ret)]

def largeOps : List (Nat × ReturnOp) :=
  [(1228, .pair), (1232, .reserve), (1236, .save9), (1240, .save10),
   (1244, .output), (1248, .statusAddress), (1252, .zero32),
   (1256, .storeStatus), (1260, .restore10), (1264, .restore9),
   (1268, .release), (1272, .ret)]

def smallResult (s : ArmState) : ArmState := returnBlock smallOps s
def largeResult (s : ArmState) : ArmState := returnBlock largeOps s

theorem small_run (s : ArmState) (base : BitVec 64)
    (code : Linked.Rebase.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 472#64) :
    run 11 s = smallResult s := by
  apply returnBlock_run smallOps s base
  · intro row member
    have included : ∀ row ∈ smallOps,
        (row.1, row.2.word) ∈ Linked.Rebase.program := by decide
    exact code _ (included row member)
  · exact error
  · exact aligned
  · change r .PC s = _ at pc
    simp [ReturnFollows, smallOps, ReturnOp.effect, put, next,
      state_simp_rules, pc, BitVec.add_assoc]

theorem large_run (s : ArmState) (base : BitVec 64)
    (code : Linked.Rebase.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 1228#64) :
    run 12 s = largeResult s := by
  apply returnBlock_run largeOps s base
  · intro row member
    have included : ∀ row ∈ largeOps,
        (row.1, row.2.word) ∈ Linked.Rebase.program := by decide
    exact code _ (included row member)
  · exact error
  · exact aligned
  · change r .PC s = _ at pc
    simp [ReturnFollows, largeOps, ReturnOp.effect, put, next,
      state_simp_rules, pc, BitVec.add_assoc]

end SszArm.Indices.RebaseReturn
