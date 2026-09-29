import SszArm.CodecMeasureSingletonBodyOps
import SszArm.MeasureResultFields

set_option autoImplicit false

namespace SszArm.Codec.Measure.Singleton.Body

open SszArm.Measure.Activation (next put)
open Delimited (MemoryFrame)

inductive ZeroPair where | reserved | right | left deriving DecidableEq

def ZeroPair.start : ZeroPair → Nat | .reserved => 168 | .right => 220 | .left => 272

def ZeroPair.offset : ZeroPair → Nat | .reserved => 48 | .right => 32 | .left => 16

def ZeroPair.ops : ZeroPair → List Op
  | .reserved => [.p168, .p172, .p176, .p180, .p184, .p188, .p192, .p196, .p200, .p204, .p208, .p212]
  | .right => [.p220, .p224, .p228, .p232, .p236, .p240, .p244, .p248, .p252, .p256, .p260, .p264]
  | .left => [.p272, .p276, .p280, .p284, .p288, .p292, .p296, .p300, .p304, .p308, .p312, .p316]

@[irreducible] def zeroStored (site : ZeroPair) (s : ArmState) : ArmState := block site.ops s

def zeroMemory (site : ZeroPair) (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 19) s + BitVec.ofNat 64 site.offset + 8#64) 0#64
    (write_mem_bytes 8 (r (.GPR 19) s + BitVec.ofNat 64 site.offset) 0#64
      (write_mem_bytes 8 (r (.GPR 31) s - 16#64 + 8#64) (r (.GPR 10) s)
        (write_mem_bytes 8 (r (.GPR 31) s - 16#64) (r (.GPR 9) s) s)))

@[simp] theorem zeroStored_program (site : ZeroPair) (s : ArmState) :
    (zeroStored site s).program = s.program := by simp [zeroStored]

@[simp] theorem zeroStored_error (site : ZeroPair) (s : ArmState) :
    read_err (zeroStored site s) = read_err s := by simp [zeroStored]

@[simp] theorem zeroStored_sp (site : ZeroPair) (s : ArmState) :
    r (.GPR 31) (zeroStored site s) = r (.GPR 31) s := by
  cases site <;> simp [zeroStored, ZeroPair.ops, block, Op.effect, next, put,
    state_simp_rules, BitVec.sub_add_cancel]

@[simp] theorem zeroStored_pc (site : ZeroPair) (s : ArmState) :
    read_pc (zeroStored site s) = read_pc s + 48#64 := by
  cases site <;> simp [zeroStored, ZeroPair.ops, block, Op.effect, next, put,
    state_simp_rules, BitVec.add_assoc]

@[simp] theorem zeroStored_memory (site : ZeroPair) (s : ArmState) :
    (zeroStored site s).mem = (zeroMemory site s).mem := by
  cases site <;> simp [zeroStored, ZeroPair.ops, ZeroPair.offset, block, Op.effect,
    next, put, zeroMemory, state_simp_rules]
  all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

@[simp] theorem zeroStored_register (site : ZeroPair) (s : ArmState) (reg : BitVec 5)
    (not9 : reg ≠ 9#5) (not10 : reg ≠ 10#5) (notStack : reg ≠ 31#5) :
    r (.GPR reg) (zeroStored site s) = r (.GPR reg) s := by
  cases site <;> simp [zeroStored, ZeroPair.ops, block, Op.effect,
    next, put, state_simp_rules, not9, not10, notStack]

@[simp] theorem zeroStored_vector (site : ZeroPair) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (zeroStored site s) = r (.SFP reg) s := by
  simpa only [zeroStored] using block_field site.ops s (.SFP reg) trivial

theorem zeroStored_aligned (site : ZeroPair) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (zeroStored site s) := by
  change Aligned (r (.GPR 31) (zeroStored site s)) 4
  rw [zeroStored_sp]
  exact BoolCodec.stack_aligned s aligned

theorem zeroStored_run (site : ZeroPair) (s : ArmState) (base : BitVec 64)
    (code : Linked.PlanSingleton.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 site.start) : run 12 s = zeroStored site s := by
  have lower := BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  rw [zeroStored]
  have length : site.ops.length = 12 := by cases site <;> rfl
  rw [← length]
  apply runs site.ops s base code error
  change r .PC s = base + BitVec.ofNat 64 site.start at pc
  cases site <;>
    simp (config := {decide := true}) [Follows, ZeroPair.ops, ZeroPair.start, Op.row,
      Op.effect, next, put, state_simp_rules, CheckSPAlignment, read_gpr,
      BitVec.setWidth_eq, pc, BitVec.add_assoc] at aligned lower ⊢
  all_goals exact ⟨aligned, lower⟩

theorem zeroStored_space (site : ZeroPair) (s : ArmState)
    (space : SszArm.Measure.Result.ErrorSpace s) :
    SszArm.Measure.Result.ErrorSpace (zeroStored site s) := by
  rcases space with ⟨low, bound, separate⟩
  constructor
  · rw [zeroStored_sp]
    exact low
  · rw [zeroStored_register site s 19#5 (by decide) (by decide) (by decide)]
    exact bound
  · rw [zeroStored_sp, zeroStored_register site s 19#5 (by decide) (by decide) (by decide)]
    exact separate

theorem zeroStored_scratch (site : ZeroPair) (s : ArmState)
    (space : SszArm.Measure.Result.ErrorSpace s) :
    r (.GPR 9) (zeroStored site s) = r (.GPR 9) s ∧
      r (.GPR 10) (zeroStored site s) = r (.GPR 10) s := by
  have nine : r (.GPR 9) (zeroStored site s) =
      read_mem_bytes 8 (r (.GPR 31) s - 16#64) (zeroMemory site s) := by
    cases site <;> simp only [zeroStored, ZeroPair.ops, ZeroPair.offset, block,
      List.foldl, Op.effect, next, put, zeroMemory, state_simp_rules]
  have ten : r (.GPR 10) (zeroStored site s) =
      read_mem_bytes 8 (r (.GPR 31) s - 16#64 + 8#64) (zeroMemory site s) := by
    cases site <;> simp only [zeroStored, ZeroPair.ops, ZeroPair.offset, block,
      List.foldl, Op.effect, next, put, zeroMemory, state_simp_rules]
  rw [nine, ten]
  rcases space with ⟨low, bound, separate⟩
  rcases separate with separate | separate <;> cases site
  all_goals
    simp only [zeroMemory, ZeroPair.offset]
    constructor
    · rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
      rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
      rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
      exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)
    · rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
      rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
        (by bv_omega) (by bv_omega) (by bv_omega)]
      exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)

def zeroWrites (site : ZeroPair) (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 31) s).toNat - 16, 16), ((r (.GPR 19) s).toNat + site.offset, 16)]

theorem zeroStored_frame (site : ZeroPair) (s : ArmState)
    (space : SszArm.Measure.Result.ErrorSpace s) :
    MemoryFrame (zeroWrites site s) s (zeroStored site s) := by
  rcases space with ⟨low, bound, separate⟩
  intro address outside
  have slot := outside ((r (.GPR 31) s).toNat - 16, 16) (by simp [zeroWrites])
  have payload := outside ((r (.GPR 19) s).toNat + site.offset, 16) (by simp [zeroWrites])
  rw [zeroStored_memory]
  cases site <;> simp only [ZeroPair.offset, Prod.fst, Prod.snd] at payload slot ⊢
  all_goals
    simp only [zeroMemory, ZeroPair.offset]
    rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)]
    rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)]
    rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)]
    exact BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)

end SszArm.Codec.Measure.Singleton.Body
