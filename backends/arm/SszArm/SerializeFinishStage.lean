import SszArm.SerializeFinishMemory

namespace SszArm.Serialize.Finish

open Delimited (MemoryFrame)

/-- Five actual loads/stores preceding the measurement-status branch. -/
def stageOps : List Op := [.p52, .p56, .p60, .p64, .p68]

def staged (base : BitVec 64) (s : ArmState) : ArmState := block base stageOps s

def stageMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (sp s + 8#64)
    (read_mem_bytes 8 (sp s + 32#64) s ++ read_mem_bytes 8 (sp s + 24#64) s) s

theorem stage_run (base : BitVec 64) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 52#64) : run 5 s = staged base s := by
  apply block_run base stageOps s code error aligned
  change r .PC s = _ at pc
  simp [Follows, stageOps, Op.row, Op.effect, next, put, state_simp_rules,
    BitVec.add_assoc, pc]

@[simp] theorem staged_pc (base : BitVec 64) (s : ArmState) :
    read_pc (staged base s) = read_pc s + 20#64 := by
  simp [staged, stageOps, block, Op.effect, put, next, state_simp_rules, BitVec.add_assoc]

@[simp] theorem staged_memory (base : BitVec 64) (s : ArmState) :
    (staged base s).mem = (stageMemory s).mem := by
  simp [staged, stageOps, block, Op.effect, put, next, stageMemory, sp, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

@[simp] theorem staged_error (base : BitVec 64) (s : ArmState) :
    read_err (staged base s) = read_err s :=
  block_error base stageOps s

@[simp] theorem staged_register (base : BitVec 64) (s : ArmState) (reg : BitVec 5)
    (unchanged : reg ∉ [5#5, 8#5, 9#5, 10#5, 11#5, 12#5]) :
    r (.GPR reg) (staged base s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at unchanged
  simp_all [staged, stageOps, block, Op.effect, put, next, state_simp_rules]

theorem staged_fields (base : BitVec 64) (s : ArmState) :
    r (.GPR 8#5) (staged base s) = read_mem_bytes 8 (sp s + 40#64) s ∧
    r (.GPR 5#5) (staged base s) = read_mem_bytes 8 (sp s + 48#64) s ∧
    r (.GPR 10#5) (staged base s) = read_mem_bytes 8 (sp s + 56#64) s ∧
    (r (.GPR 9#5) (staged base s)).setWidth 32 = read_mem_bytes 4 (sp s + 88#64) s := by
  simp [staged, stageOps, block, Op.effect, put, next, sp, state_simp_rules,
    BitVec.setWidth_setWidth_of_le]

/-- This branch is settled solely by the just-returned measurement status. -/
def branched (base : BitVec 64) (s : ArmState) : ArmState :=
  w .PC (if read_mem_bytes 4 (sp s + 88#64) s = 0#32
    then base + 136#64 else base + 76#64) (staged base s)

@[simp] theorem branched_error (base : BitVec 64) (s : ArmState) :
    read_err (branched base s) = read_err s := by
  calc
    read_err (branched base s) = read_err (staged base s) := by
      simp [branched, state_simp_rules]
    _ = read_err s := staged_error base s

theorem branch_run (base : BitVec 64) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 52#64) : run 6 s = branched base s := by
  have follows : Follows base (stageOps ++ [.p72]) s := by
    change r .PC s = _ at pc
    simp [Follows, stageOps, Op.row, Op.effect, next, put, state_simp_rules,
      BitVec.add_assoc, pc]
  have execution := block_run base (stageOps ++ [.p72]) s code error aligned follows
  change run 6 s = _ at execution
  rw [execution]
  simp [branched, staged, stageOps, block, Op.effect, next, put, sp,
    state_simp_rules, BitVec.setWidth_setWidth_of_le]

def successOps : List Op := [.p136, .p140, .p144, .p148]

def successStage (base : BitVec 64) (s : ArmState) : ArmState :=
  block base successOps (branched base s)

/-- Staging succeeds independently of the later host-size conversion and capacity check. -/
theorem success_stage_run (base : BitVec 64) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 52#64)
    (status : read_mem_bytes 4 (sp s + 88#64) s = 0#32) :
    run 10 s = successStage base s := by
  rw [show 10 = 6 + 4 by decide, run_plus, branch_run base s code error aligned pc]
  apply block_run base successOps (branched base s)
  · exact code.congr (by simp [branched, staged, state_simp_rules])
  · exact (branched_error base s).trans error
  · simpa [branched, staged, stageOps, block, Op.effect, put, next,
      CheckSPAlignment, read_gpr, state_simp_rules] using aligned
  · simp [Follows, successOps, branched, Op.row, Op.effect, next, put,
      state_simp_rules, status, BitVec.add_assoc]

@[simp] theorem success_stage_pc (base : BitVec 64) (s : ArmState)
    (status : read_mem_bytes 4 (sp s + 88#64) s = 0#32) :
    read_pc (successStage base s) = base + 152#64 := by
  simp [successStage, successOps, branched, block, Op.effect, next, put,
    state_simp_rules, status, BitVec.add_assoc]

theorem success_stage_fields (base : BitVec 64) (s : ArmState) :
    r (.GPR 8#5) (successStage base s) = read_mem_bytes 8 (sp s + 40#64) s ∧
    r (.GPR 5#5) (successStage base s) = read_mem_bytes 8 (sp s + 48#64) s ∧
    r (.GPR 10#5) (successStage base s) = read_mem_bytes 8 (sp s + 56#64) s := by
  simpa [successStage, successOps, branched, block, Op.effect, next, put,
    state_simp_rules] using
      ⟨(staged_fields base s).1, (staged_fields base s).2.1, (staged_fields base s).2.2.1⟩

@[simp] theorem success_stage_register (base : BitVec 64) (s : ArmState) (reg : BitVec 5)
    (unchanged : reg ∉ [5#5, 8#5, 9#5, 10#5, 11#5, 12#5]) :
    r (.GPR reg) (successStage base s) = r (.GPR reg) s := by
  have keep := staged_register base s reg unchanged
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at unchanged
  simpa [successStage, successOps, branched, block, Op.effect, next, put,
    state_simp_rules, unchanged.2.2.1, unchanged.2.2.2.2.1] using keep

@[simp] theorem success_stage_program (base : BitVec 64) (s : ArmState) :
    (successStage base s).program = s.program := by
  simp [successStage, branched, staged, state_simp_rules]

@[simp] theorem success_stage_error (base : BitVec 64) (s : ArmState) :
    read_err (successStage base s) = read_err s := by
  rw [successStage, block_error, branched_error]

@[simp] theorem success_stage_vector (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (successStage base s) = r (.SFP reg) s := by
  simp [successStage, branched, staged, state_simp_rules]

macro "serialize_finish_side" : tactic => `(tactic|
  first | assumption | omega | bv_omega)

theorem stage_frame (base : BitVec 64) (s : ArmState)
    (physical : (sp s).toNat + 24 ≤ 2^64) :
    MemoryFrame [((sp s).toNat + 8, 16)] s (staged base s) := by
  intro address outside
  have apart := outside ((sp s).toNat + 8, 16) (by simp)
  rw [staged_memory]
  exact BoolCodec.write_mem_bytes_frame _ _ _ _ _ (by bv_omega) (by bv_omega)

def successMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (sp s + 24#64) (read_mem_bytes 16 (sp s + 24#64) s)
    (write_mem_bytes 8 (sp s + 56#64) (read_mem_bytes 8 (sp s + 56#64) s)
      (write_mem_bytes 16 (sp s + 40#64) (read_mem_bytes 16 (sp s + 40#64) s)
        (stageMemory s)))

private theorem success_block_memory (base : BitVec 64) (s : ArmState) :
    (block base successOps s).mem =
      (write_mem_bytes 16 (sp s + 24#64)
        (read_mem_bytes 8 (sp s + 16#64) s ++ read_mem_bytes 8 (sp s + 8#64) s)
        (write_mem_bytes 8 (sp s + 56#64) (r (.GPR 10#5) s)
          (write_mem_bytes 16 (sp s + 40#64)
            (r (.GPR 5#5) s ++ r (.GPR 8#5) s) s))).mem := by
  simp [successOps, block, Op.effect, next, put, sp, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem success_stage_memory (base : BitVec 64) (s : ArmState)
    (physical : (sp s).toNat + 64 ≤ 2^64) :
    (successStage base s).mem = (successMemory s).mem := by
  have stagePair : stageMemory s =
      write_mem_bytes 8 (sp s + 16#64) (read_mem_bytes 8 (sp s + 32#64) s)
        (write_mem_bytes 8 (sp s + 8#64) (read_mem_bytes 8 (sp s + 24#64) s) s) := by
    unfold stageMemory
    rw [UintCodec.Tail.write_pair_words _ _ _ _ (by bv_omega)]
    simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have stageLow : read_mem_bytes 8 (sp s + 8#64) (staged base s) =
      read_mem_bytes 8 (sp s + 24#64) s := by
    rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp (staged_memory base s), stagePair]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8
      (sp s + 8#64) (sp s + 16#64) _ (by bv_omega) (by bv_omega) (by left; bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)
  have stageHigh : read_mem_bytes 8 (sp s + 16#64) (staged base s) =
      read_mem_bytes 8 (sp s + 32#64) s := by
    rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp (staged_memory base s), stagePair]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)
  have stageSP := staged_register base s 31#5 (by decide)
  have fields := staged_fields base s
  rw [successStage, success_block_memory]
  simp [branched, sp, state_simp_rules, stageSP,
    fields.1, fields.2.1, fields.2.2.1, stageLow, stageHigh,
    successMemory, BoolCodec.pair_read, BitVec.add_assoc]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem,
    staged_memory, stageMemory]

/-- The Plan stores write back their original bytes; only the staging slot changes. -/
theorem success_stage_frame (base : BitVec 64) (s : ArmState)
    (physical : (sp s).toNat + 64 ≤ 2^64) :
    MemoryFrame [((sp s).toNat + 8, 16)] s (successStage base s) := by
  have initial : MemoryFrame [((sp s).toNat + 8, 16)] s (stageMemory s) := by
    intro address outside
    rw [← staged_memory base s]
    exact stage_frame base s (by omega) address outside
  have first := observed_store_frame s (stageMemory s) _ initial (sp s + 40#64) 16 (by bv_omega)
  have second := observed_store_frame s _ _ first (sp s + 56#64) 8 (by bv_omega)
  have third := observed_store_frame s _ _ second (sp s + 24#64) 16 (by bv_omega)
  intro address outside
  rw [success_stage_memory base s physical]
  exact third address outside

/-- Reads of the five initialized Plan words after the physical staging stores. -/
theorem success_stage_plan (base : BitVec 64) (s : ArmState)
    (physical : (sp s).toNat + 96 ≤ 2^64) (index : Fin 5) :
    read_mem_bytes 8 (sp s + BitVec.ofNat 64 (24 + 8 * index.val)) (successStage base s) =
      read_mem_bytes 8 (sp s + BitVec.ofNat 64 (24 + 8 * index.val)) s := by
  have frame := success_stage_frame base s (by omega)
  have indexBound := index.isLt
  apply frame.read
  · bv_omega
  · right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    right
    dsimp
    bv_omega

end SszArm.Serialize.Finish
