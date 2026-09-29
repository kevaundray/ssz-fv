import SszArm.NatMulBounds
import SszArm.NatMulProductCarry
import SszArm.NatMulLoopStoreFrame
import SszArm.NatMulLoopLoadFrame
import SszArm.NatMulHighProduct

namespace SszArm.NatMul

/-- Scalar and execution state preserved across a body stage. The changed set
contains only real instruction destinations; SP is never an allowed change. -/
structure LoopStable (changed : List (BitVec 5)) (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, reg ∉ changed → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem LoopStable.refl (changed : List (BitVec 5)) (s : ArmState) :
    LoopStable changed s s := ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem LoopStable.trans {changed : List (BitVec 5)} {s t u : ArmState}
    (st : LoopStable changed s t) (tu : LoopStable changed t u) :
    LoopStable changed s u :=
  ⟨tu.program.trans st.program, tu.error.trans st.error, tu.sp.trans st.sp,
    fun reg h => (tu.registers reg h).trans (st.registers reg h),
    fun reg => (tu.vectors reg).trans (st.vectors reg)⟩

theorem LoopStable.weaken {small large : List (BitVec 5)} {s t : ArmState}
    (frame : LoopStable small s t) (contained : ∀ reg ∈ small, reg ∈ large) :
    LoopStable large s t :=
  ⟨frame.program, frame.error, frame.sp,
    fun reg h => frame.registers reg (fun hs => h (contained reg hs)), frame.vectors⟩

theorem LoopStable.code {changed : List (BitVec 5)} {s t : ArmState}
    (frame : LoopStable changed s t) {base : BitVec 64} (code : CodeAt s base) :
    CodeAt t base := by simpa only [CodeAt, frame.program] using code

theorem LoopStable.aligned {changed : List (BitVec 5)} {s t : ArmState}
    (frame : LoopStable changed s t) (aligned : CheckSPAlignment s) :
    CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using aligned

def loopInit (base : BitVec 64) (s : ArmState) : ArmState :=
  block base [.p580, .p584, .p588, .p592, .p596] s

theorem loop_init_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 580#64) : run 5 s = loopInit base s := by
  change r .PC s = base + 580#64 at pc
  apply block_run base [.p580, .p584, .p588, .p592, .p596] s code error aligned
  simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, pc, BitVec.add_assoc]

theorem loop_init_values (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 580#64) :
    read_pc (loopInit base s) = base + 600#64 ∧
    r (.GPR 8#5) (loopInit base s) = r (.GPR 27#5) s ∧
    r (.GPR 9#5) (loopInit base s) = r (.GPR 26#5) s ∧
    r (.GPR 10#5) (loopInit base s) = r (.GPR 28#5) s ∧
    r (.GPR 11#5) (loopInit base s) = r (.GPR 20#5) s ∧
    r (.GPR 12#5) (loopInit base s) = 0#64 := by
  change r .PC s = base + 580#64 at pc
  simp [loopInit, block, Op.effect, put, next, state_simp_rules, pc, BitVec.add_assoc]

theorem loop_init_stable (s : ArmState) (base : BitVec 64) :
    LoopStable [8#5, 9#5, 10#5, 11#5, 12#5] s (loopInit base s) := by
  constructor
  · simp [loopInit]
  · simp [loopInit]
  · simp [loopInit, block, Op.effect, put, next, state_simp_rules]
  · intro reg different
    simp_all [loopInit, block, Op.effect, put, next, state_simp_rules]
  · intro reg
    unfold loopInit block
    exact NatMulStateFold.preserves (fun t (op : Op) => op.effect base t) (r (.SFP reg))
      ([.p580, .p584, .p588, .p592, .p596] : List Op) s (fun op _ t => op.sfp base t reg)

theorem loop_init_memory (s : ArmState) (base : BitVec 64) :
    (loopInit base s).mem = s.mem := by
  simp [loopInit, block, Op.effect, put, next, state_simp_rules]

def loopRowInit (base : BitVec 64) (s : ArmState) : ArmState :=
  block base [.p664, .p668, .p672, .p676] s

theorem loop_row_init_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 664#64) : run 4 s = loopRowInit base s := by
  change r .PC s = base + 664#64 at pc
  apply block_run base [.p664, .p668, .p672, .p676] s code error aligned
  simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, pc, BitVec.add_assoc]

def loopAdds (base : BitVec 64) (s : ArmState) : ArmState :=
  block base [.p872, .p876, .p880, .p884] s

theorem loop_adds_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 872#64) : run 4 s = loopAdds base s := by
  change r .PC s = base + 872#64 at pc
  apply block_run base [.p872, .p876, .p880, .p884] s code error aligned
  simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, pc, BitVec.add_assoc]

/-- The carry branch is deliberately separate from the store: the store must
preserve the ADDS flags, which are consumed at +920. -/
def loopCarryOps (s : ArmState) : List Op :=
  if r (.FLAG .C) s = 1#1 then [.p920, .p932] else [.p920, .p924, .p928]

def loopCarried (base : BitVec 64) (s : ArmState) : ArmState :=
  w .PC (base + 936#64)
    (w (.GPR 15#5) (r (.GPR 17#5) s + if r (.FLAG .C) s = 1#1 then 1#64 else 0#64) s)

theorem loop_carry_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 920#64) :
    run (loopCarryOps s).length s = loopCarried base s := by
  change r .PC s = base + 920#64 at pc
  have follows : Follows base (loopCarryOps s) s := by
    unfold loopCarryOps
    split <;> simp_all [Follows, Op.row, Op.effect, put, next, state_simp_rules, BitVec.add_assoc]
  rw [block_run base (loopCarryOps s) s code error aligned follows]
  unfold loopCarryOps
  split <;> simp_all [loopCarried, block, Op.effect, put, next, NatAdd.load_gpr_pc,
    state_simp_rules, BitVec.add_assoc]

def loopColumn (base : BitVec 64) (s : ArmState) : ArmState :=
  block base [.p936, .p940, .p944, .p948] s

theorem loop_column_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 936#64) : run 4 s = loopColumn base s := by
  change r .PC s = base + 936#64 at pc
  apply block_run base [.p936, .p940, .p944, .p948] s code error aligned
  simp [Follows, Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
    state_simp_rules, pc, BitVec.add_assoc]

theorem loop_column_pc (s : ArmState) (base : BitVec 64) :
    read_pc (loopColumn base s) =
      if r (.GPR 25#5) s = r (.GPR 0#5) s then base + 952#64 else base + 680#64 := by
  simp [loopColumn, block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
    state_simp_rules, Udivti3.cmp_zero]

def loopRowAdvance (base : BitVec 64) (s : ArmState) : ArmState :=
  block base [.p964, .p968, .p972] s

theorem loop_row_advance_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 964#64) : run 3 s = loopRowAdvance base s := by
  change r .PC s = base + 964#64 at pc
  apply block_run base [.p964, .p968, .p972] s code error aligned
  simp [Follows, Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
    state_simp_rules, pc, BitVec.add_assoc]

/-- +1012 is a real executed branch, not a relabeling of the final row. -/
theorem loop_exit_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1012#64) :
    run 1 s = w .PC (base + 1060#64) s := by
  change stepi s = _
  exact step s base .p1012 code pc error aligned

end SszArm.NatMul
