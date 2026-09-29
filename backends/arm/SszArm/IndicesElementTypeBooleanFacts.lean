import SszArm.IndicesElementTypeBooleanBody

set_option autoImplicit false

namespace SszArm.Indices.ElementType.BooleanBody

@[simp] theorem block_program (ops : List Op) (s : ArmState) :
    (block ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction => exact (induction _).trans (op.program s)

@[simp] theorem block_error (ops : List Op) (s : ArmState) :
    read_err (block ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction => exact (induction _).trans (op.error s)

theorem block_aligned (ops : List Op) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (block ops s) := by
  induction ops generalizing s with
  | nil => exact aligned
  | cons op ops induction => exact induction _ (op.aligned s aligned)

@[simp] theorem body_pc (s : ArmState) :
    read_pc (block ops s) = read_pc s + 76#64 := by
  simp [block, ops, Op.effect, next, put, state_simp_rules, BitVec.add_assoc]

@[simp] theorem body_sp (s : ArmState) :
    r (.GPR 31#5) (block ops s) = r (.GPR 31#5) s := by
  simp [block, ops, Op.effect, next, put, state_simp_rules]

theorem Op.register (op : Op) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [9#5, 10#5, 31#5]) :
    r (.GPR reg) (op.effect s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched
  cases op <;> simp [Op.effect, next, put, state_simp_rules,
    untouched.1, untouched.2.1, untouched.2.2]

theorem block_register (ops : List Op) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [9#5, 10#5, 31#5]) :
    r (.GPR reg) (block ops s) = r (.GPR reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction => exact (induction _).trans (op.register s reg untouched)

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, next, put, state_simp_rules]

@[simp] theorem block_vector (ops : List Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (block ops s) = r (.SFP reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction => exact (induction _).trans (op.vector s reg)

/-- Executes both real stores and the original restore/RET exit. -/
theorem body_return_run (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 60#64) :
    run 21 s = returned (block ops s) := by
  have body := body_run s base code error aligned pc
  have tail := return_run .boolean (block ops s) base
    (Codec.Linked.WordsAt.preserve code (block_program ops s))
    ((block_error ops s).trans error) (block_aligned ops s aligned)
    (by simp [body_pc, pc, ReturnSite.offset, BitVec.add_assoc])
  change run (19 + 2) s = _
  rw [run_plus, body]
  exact tail

end SszArm.Indices.ElementType.BooleanBody
