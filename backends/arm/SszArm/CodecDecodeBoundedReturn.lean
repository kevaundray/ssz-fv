import SszArm.CodecDecodeBoundedStatus

namespace SszArm.Codec.Decode.Bounded

inductive ReturnKind where
  | failure | success
  deriving DecidableEq

def ReturnKind.start : ReturnKind → Nat
  | .failure => 180
  | .success => 236

def ReturnKind.ops : ReturnKind → List Op
  | .failure => [.p180, .p184, .p188, .p192]
  | .success => [.p236, .p240, .p244, .p248]

def restored (s : ArmState) : ArmState :=
  let sp := r (.GPR 31#5) s
  let link := read_mem_bytes 8 sp s
  w .PC link
    (w (.GPR 31#5) (sp + 48#64)
      (w (.GPR 30#5) link
        (w (.GPR 21#5) (read_mem_bytes 8 (sp + 24#64) s)
          (w (.GPR 22#5) (read_mem_bytes 8 (sp + 16#64) s)
            (w (.GPR 19#5) (read_mem_bytes 8 (sp + 40#64) s)
              (w (.GPR 20#5) (read_mem_bytes 8 (sp + 32#64) s) s))))))

theorem restore_effect (s : ArmState) (base : BitVec 64) (kind : ReturnKind) :
    block base kind.ops s = restored s := by
  cases kind <;> apply state_eq_iff_components_eq.mpr
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · intro field
      cases field with
      | GPR reg =>
        by_cases r19 : reg = 19#5 <;> by_cases r20 : reg = 20#5 <;>
          by_cases r21 : reg = 21#5 <;> by_cases r22 : reg = 22#5 <;>
          by_cases r30 : reg = 30#5 <;> by_cases r31 : reg = 31#5 <;>
          (try subst reg) <;>
          simp_all [block, ReturnKind.ops, Op.effect, loadPair, restoreLR, put, next,
            restored, state_simp_rules, BitVec.add_assoc]
      | PC => simp [block, ReturnKind.ops, Op.effect, loadPair, restoreLR, put, next,
          restored, state_simp_rules, BitVec.add_assoc]
      | SFP reg => simp [block, ReturnKind.ops, Op.effect, loadPair, restoreLR, put, next,
          restored, state_simp_rules]
      | FLAG flag => simp [block, ReturnKind.ops, Op.effect, loadPair, restoreLR, put, next,
          restored, state_simp_rules]
      | ERR => simp [block, ReturnKind.ops, Op.effect, loadPair, restoreLR, put, next,
          restored, state_simp_rules]
    · simp [block, ReturnKind.ops, Op.effect, loadPair, restoreLR, put, next,
        restored, state_simp_rules]
    · intro width address
      simp [block, ReturnKind.ops, Op.effect, loadPair, restoreLR, put, next,
        restored, state_simp_rules]

theorem restore_run (s : ArmState) (base : BitVec 64) (kind : ReturnKind)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.start) : run 4 s = restored s := by
  have follows : Follows base kind.ops s := by
    change r .PC s = _ at pc
    cases kind <;>
      simp [ReturnKind.ops, ReturnKind.start, Follows, Op.row, Op.effect,
        put, next, loadPair, restoreLR, state_simp_rules, pc, BitVec.add_assoc]
  have execution := block_run base kind.ops s code error aligned follows
  have count : kind.ops.length = 4 := by cases kind <;> rfl
  rw [count] at execution
  exact execution.trans (restore_effect s base kind)

@[simp] theorem restored_pc (s : ArmState) :
    read_pc (restored s) = read_mem_bytes 8 (r (.GPR 31#5) s) s := by
  simp [restored, state_simp_rules]

@[simp] theorem restored_sp (s : ArmState) :
    r (.GPR 31#5) (restored s) = r (.GPR 31#5) s + 48#64 := by
  simp [restored, state_simp_rules]

@[simp] theorem restored_memory (s : ArmState) : (restored s).mem = s.mem := by
  simp [restored, state_simp_rules]

@[simp] theorem restored_program (s : ArmState) : (restored s).program = s.program := by
  simp [restored, state_simp_rules]

@[simp] theorem restored_error (s : ArmState) : read_err (restored s) = read_err s := by
  simp [restored, state_simp_rules]

@[simp] theorem restored_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (restored s) = r (.SFP reg) s := by
  simp [restored, state_simp_rules]

theorem restored_register (s : ArmState) (reg : BitVec 5)
    (outside : reg ∉ [19#5, 20#5, 21#5, 22#5, 30#5, 31#5]) :
    r (.GPR reg) (restored s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  simp (disch := simp_all) [restored, state_simp_rules]

/-- Both the native success status and its actual restoring RET are executed. -/
theorem success_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 196#64) :
    run 14 s = restored (Emit.statusStored s) := by
  have status := status_run s base code error aligned pc
  have nextCode : CodeAt (Emit.statusStored s) base := by
    simpa only [CodeAt, Linked.Bounded.CodeAt, Linked.WordsAt, Emit.statusStored_program] using code
  have nextPC : read_pc (Emit.statusStored s) = base + 236#64 := by
    rw [Emit.statusStored_pc, pc]
    simp [BitVec.add_assoc]
  rw [show 14 = 10 + 4 by decide, run_plus, status]
  exact restore_run _ base .success nextCode (by simpa using error)
    (Emit.statusStored_aligned s aligned) nextPC

end SszArm.Codec.Decode.Bounded
