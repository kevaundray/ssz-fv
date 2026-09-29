import SszArm.CodecDecodeBoundedReturn

namespace SszArm.Codec.Decode.Bounded

/-- Split only at real straight-line phase boundaries. Neither phase is a
semantic constructor: every typed-error store is an executed raw instruction. -/
inductive ErrorStage where
  | expected | tag | actual
  deriving DecidableEq

def ErrorStage.start : ErrorStage → Nat
  | .expected => 68
  | .tag => 76
  | .actual => 116

def ErrorStage.ops : ErrorStage → List Op
  | .expected => [.p68, .p72]
  | .tag => [.p76, .p80, .p84, .p88, .p92, .p96, .p100, .p104, .p108, .p112]
  | .actual => [.p116, .p120, .p124, .p128, .p132, .p136, .p140, .p144,
      .p148, .p152, .p156, .p160, .p164, .p168, .p172, .p176]

def ErrorStage.stop : ErrorStage → Nat
  | .expected => 76
  | .tag => 116
  | .actual => 180

def ErrorStage.result (stage : ErrorStage) (s : ArmState) (base : BitVec 64) : ArmState :=
  block base stage.ops s

theorem error_stage_follows (stage : ErrorStage) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) : Follows base stage.ops s := by
  change r .PC s = _ at pc
  cases stage <;>
    simp [ErrorStage.ops, ErrorStage.start, Follows, Op.row, Op.effect,
      put, next, loadPair, state_simp_rules, pc, BitVec.add_assoc]

theorem error_stage_run (stage : ErrorStage) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    run stage.ops.length s = stage.result s base :=
  block_run base stage.ops s code error aligned (error_stage_follows stage s base pc)

theorem error_stage_pc (stage : ErrorStage) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    read_pc (stage.result s base) = base + BitVec.ofNat 64 stage.stop := by
  change r .PC s = _ at pc
  cases stage <;> simp [ErrorStage.result, ErrorStage.ops, ErrorStage.start, ErrorStage.stop,
    block, Op.effect, put, next, loadPair, state_simp_rules, pc, BitVec.add_assoc]

@[simp] theorem error_stage_sp (stage : ErrorStage) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (stage.result s base) = r (.GPR 31#5) s := by
  cases stage <;> simp [ErrorStage.result, ErrorStage.ops, block, Op.effect,
    put, next, loadPair, state_simp_rules, BitVec.sub_add_cancel]

@[simp] theorem error_stage_program (stage : ErrorStage) (s : ArmState) (base : BitVec 64) :
    (stage.result s base).program = s.program := by
  cases stage <;> simp [ErrorStage.result, ErrorStage.ops, block]

@[simp] theorem error_stage_error (stage : ErrorStage) (s : ArmState) (base : BitVec 64) :
    read_err (stage.result s base) = read_err s := by
  cases stage <;> simp [ErrorStage.result, ErrorStage.ops, block]

theorem error_stage_register (stage : ErrorStage) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (outside : reg ∉ [8#5, 9#5, 10#5, 31#5]) :
    r (.GPR reg) (stage.result s base) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  cases stage <;> simp (disch := simp_all) [ErrorStage.result, ErrorStage.ops, block,
    Op.effect, put, next, loadPair, state_simp_rules]

theorem error_stage_aligned (stage : ErrorStage) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (stage.result s base) := by
  simpa only [CheckSPAlignment, state_simp_rules, error_stage_sp] using aligned

/-- The complete failure-side store sequence and restoring RET execute without
allocating, rolling back an arena, or initializing trailing result padding. -/
theorem error_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 68#64) :
    run 32 s = restored (ErrorStage.actual.result
      (ErrorStage.tag.result (ErrorStage.expected.result s base) base) base) := by
  let a := ErrorStage.expected.result s base
  let b := ErrorStage.tag.result a base
  let c := ErrorStage.actual.result b base
  have aRun : run 2 s = a := error_stage_run .expected s base code error aligned pc
  have aCode : CodeAt a base := by
    simpa only [a, CodeAt, Linked.Bounded.CodeAt, Linked.WordsAt, error_stage_program] using code
  have bRun : run 10 a = b := error_stage_run .tag a base aCode
    (by simpa [a] using error) (error_stage_aligned .expected s base aligned)
    (error_stage_pc .expected s base pc)
  have bCode : CodeAt b base := by
    simpa only [b, CodeAt, Linked.Bounded.CodeAt, Linked.WordsAt, error_stage_program] using aCode
  have bPC : read_pc b = base + 116#64 :=
    error_stage_pc .tag a base (error_stage_pc .expected s base pc)
  have cRun : run 16 b = c := error_stage_run .actual b base bCode
    (by simpa [b, a] using error)
    (error_stage_aligned .tag a base (error_stage_aligned .expected s base aligned)) bPC
  have cCode : CodeAt c base := by
    simpa only [c, CodeAt, Linked.Bounded.CodeAt, Linked.WordsAt, error_stage_program] using bCode
  have finish : run 4 c = restored c := restore_run c base .failure cCode
    (by simpa [c, b, a] using error)
    (error_stage_aligned .actual b base
      (error_stage_aligned .tag a base (error_stage_aligned .expected s base aligned)))
    (error_stage_pc .actual b base bPC)
  rw [show 32 = 2 + 10 + 16 + 4 by decide, run_plus, run_plus, run_plus,
    aRun, bRun, cRun, finish]

end SszArm.Codec.Decode.Bounded
