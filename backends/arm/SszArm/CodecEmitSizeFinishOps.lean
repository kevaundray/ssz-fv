import SszArm.CodecEmitSizeScan
import SszArm.EmitUintWidthLow

namespace SszArm.Codec.Emit.Size

open SszArm.Emit.Uint

/-- The size conversion borrows the same lowering slot as the shared narrowing
scan, and additionally replaces its callee-saved size register x19. -/
structure Frame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5, 11#5, 12#5, 19#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ address : BitVec 64,
    address.toNat < (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ address.toNat → t.mem address = s.mem address

theorem Frame.refl (s : ArmState) : Frame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem Frame.sp {s t : ArmState} (frame : Frame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := frame.registers _ (by decide)

theorem Frame.trans {s t u : ArmState} (first : Frame s t) (second : Frame t u) : Frame s u := by
  refine ⟨second.program.trans first.program, second.error.trans first.error,
    fun reg outside => (second.registers reg outside).trans (first.registers reg outside),
    fun reg => (second.vectors reg).trans (first.vectors reg), ?_⟩
  intro address outside
  exact (second.memory address (by simpa only [first.sp] using outside)).trans
    (first.memory address outside)

theorem Frame.of_narrow {s t : ArmState} (frame : NatNarrow.Frame s t) : Frame s t := by
  refine ⟨frame.program, frame.error, ?_, frame.vectors, frame.memory⟩
  intro reg outside
  apply frame.registers
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢
  tauto

theorem Frame.code {s t : ArmState} (frame : Frame s t) {base : BitVec 64}
    (code : Linked.EmitParts.CodeAt s base) : Linked.EmitParts.CodeAt t base :=
  Linked.WordsAt.preserve code frame.program

theorem Frame.aligned {s t : ArmState} (frame : Frame s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using aligned

inductive Op where
  | p184 | p188 | p244 | p248 | p252 | p260 | p264
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p184 => (184, 0xb40002a8#32)
  | .p188 => (188, 0xd100066a#32)
  | .p244 => (244, 0x91000529#32)
  | .p248 => (248, 0xf100053f#32)
  | .p252 => (252, 0x54000060#32)
  | .p260 => (260, 0xb4000053#32)
  | .p264 => (264, 0xf9400113#32)

def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p184, s => w .PC (if r (.GPR 8#5) s = 0#64 then base + 268#64 else base + 188#64) s
  | .p188, s => put 10 (r (.GPR 19#5) s - 1#64) s
  | .p244, s => put 9 (r (.GPR 9#5) s + 1#64) s
  | .p248, s => SszArm.Emit.Dispatch.compare64 (r (.GPR 9#5) s) 1#64 s
  | .p252, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 264#64 else base + 256#64) s
  | .p260, s => w .PC (if r (.GPR 19#5) s = 0#64 then base + 268#64 else base + 264#64) s
  | .p264, s => put 19 (read_mem_bytes 8 (r (.GPR 8#5) s) s) s

theorem fetched (s : ArmState) (base : BitVec 64) (op : Op)
    (code : Linked.EmitParts.CodeAt s base) :
    s.program.find? (base + BitVec.ofNat 64 op.row.1) = some op.row.2 := by
  cases op <;> first
    | exact Linked.EmitParts.chunk0_codeAt code _ (by decide)
    | exact Linked.EmitParts.chunk1_codeAt code _ (by decide)

theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect base s := by
  have word := fetched s base op code
  cases op
  all_goals
    simp only [Op.row] at pc word
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans word) rfl]
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, SszArm.Emit.Dispatch.next, SszArm.Emit.Dispatch.compare64,
        exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned, pc,
        BitVec.add_assoc, BitVec.sub_eq_add_neg, BitVec.setWidth_eq, apply_ite]
  all_goals first | rfl | exact w_of_w_commute (by decide) | (split <;> simp_all)

theorem Op.frame (op : Op) (base : BitVec 64) (s : ArmState) : Frame s (op.effect base s) := by
  cases op
  all_goals
    constructor
    · simp [Op.effect, put, next, SszArm.Emit.Dispatch.next,
        SszArm.Emit.Dispatch.compare64, state_simp_rules]
    · simp [Op.effect, put, next, SszArm.Emit.Dispatch.next,
        SszArm.Emit.Dispatch.compare64, state_simp_rules]
    · intro reg outside
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      simp (disch := simp_all) [Op.effect, put, next, SszArm.Emit.Dispatch.next,
        SszArm.Emit.Dispatch.compare64, state_simp_rules]
    · intro reg
      simp [Op.effect, put, next, SszArm.Emit.Dispatch.next,
        SszArm.Emit.Dispatch.compare64, state_simp_rules]
    · intro address outside
      simp [Op.effect, put, next, SszArm.Emit.Dispatch.next,
        SszArm.Emit.Dispatch.compare64, state_simp_rules]

def block (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect base s)

theorem runs (base : BitVec 64) (ops : List Op) (s : ArmState)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (follows : Follows base ops s) :
    run ops.length s = block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block base ops (op.effect base s)
    rw [run, step s base op code error aligned follows.1]
    exact ih _ ((op.frame base s).code code) ((op.frame base s).error.trans error)
      ((op.frame base s).aligned aligned) follows.2

theorem block_frame (base : BitVec 64) (ops : List Op) (s : ArmState) : Frame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact Frame.refl s
  | cons op ops ih => exact (op.frame base s).trans (ih _)

theorem block_memory (base : BitVec 64) (ops : List Op) (s : ArmState) :
    (block base ops s).mem = s.mem := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    rw [show block base (op :: ops) s = block base ops (op.effect base s) from rfl, ih]
    cases op <;> simp [Op.effect, put, next, SszArm.Emit.Dispatch.next,
      SszArm.Emit.Dispatch.compare64, state_simp_rules]

theorem block_narrow (base : BitVec 64) (ops : List Op) (s : ArmState)
    (noLoad : Op.p264 ∉ ops) : NatNarrow.Frame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact NatNarrow.Frame.refl s
  | cons op ops ih =>
    have different : op ≠ .p264 := by intro same; subst op; exact noLoad List.mem_cons_self
    have frame : NatNarrow.Frame s (op.effect base s) := by
      refine ⟨(op.frame base s).program, (op.frame base s).error, ?_,
        (op.frame base s).vectors, (op.frame base s).memory⟩
      intro reg outside
      cases op <;> simp_all only [reduceCtorEq]
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
        simp (disch := simp_all) [Op.effect, put, next, SszArm.Emit.Dispatch.next,
          SszArm.Emit.Dispatch.compare64, state_simp_rules]
    exact frame.trans (ih _ (fun member => noLoad (List.mem_cons_of_mem _ member)))

end SszArm.Codec.Emit.Size
