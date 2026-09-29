import SszArm.CodecMeasureSingletonActivation

set_option autoImplicit false

namespace SszArm.Codec.Measure.Singleton

open Activation (Exit)
open SszArm.Measure.Activation (next put)
open SszArm.Measure.ReturnBlock (restore)

def restoreOps (site : Exit) : List Activation.Op :=
  [.restorePair site, .restoreLink site, .ret site]

@[irreducible] def restored (site : Exit) (s : ArmState) : ArmState :=
  Activation.block (restoreOps site) s

@[simp] theorem restored_program (site : Exit) (s : ArmState) :
    (restored site s).program = s.program := by
  simp [restored, restoreOps, Activation.block]

@[simp] theorem restored_error (site : Exit) (s : ArmState) :
    read_err (restored site s) = read_err s := by
  simp [restored, restoreOps, Activation.block]

@[simp] theorem restored_memory (site : Exit) (s : ArmState) :
    (restored site s).mem = s.mem := by
  simp [restored, restoreOps, Activation.block, Activation.Op.effect,
    next, put, restore, state_simp_rules]

@[simp] theorem restored_vector (site : Exit) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (restored site s) = r (.SFP reg) s := by
  simp [restored, restoreOps, Activation.block, Activation.Op.effect,
    next, put, restore, state_simp_rules]

theorem restored_run (site : Exit) (s : ArmState) (base : BitVec 64)
    (code : Linked.PlanSingleton.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 site.pc) : run 3 s = restored site s := by
  have first := BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)
  have second := BoolCodec.aligned_add16 _ first
  have afterSP : Aligned (r (.GPR 31) s + 32#64) 4 := by
    simpa only [BitVec.add_assoc, BitVec.ofNat_add_ofNat] using second
  rw [restored]
  apply Activation.runs (restoreOps site) s base code error
  change r .PC s = base + BitVec.ofNat 64 site.pc at pc
  cases site <;>
    simp (config := {decide := true})
      [Activation.Follows, restoreOps, Activation.Op.row, Activation.Exit.pc,
        Activation.Op.effect, next, put, restore, state_simp_rules, CheckSPAlignment,
        read_gpr, BitVec.setWidth_eq, pc, BitVec.add_assoc] at aligned afterSP ⊢
  all_goals exact ⟨aligned, afterSP⟩

structure RestoreReady (entry current : ArmState) : Prop where
  stack : r (.GPR 31) current = bodySP entry
  link : read_mem_bytes 8 (bodySP entry) current = r (.GPR 30) entry
  twenty : read_mem_bytes 8 (bodySP entry + 16#64) current = r (.GPR 20) entry
  nineteen : read_mem_bytes 8 (bodySP entry + 24#64) current = r (.GPR 19) entry
  untouched : ∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 30 →
    reg ≠ 19#5 → reg ≠ 20#5 → reg ≠ 30#5 → r (.GPR reg) current = r (.GPR reg) entry
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) current).setWidth 64 = (r (.SFP reg) entry).setWidth 64

theorem restored_returns (site : Exit) (entry current : ArmState)
    (ready : RestoreReady entry current) (error : read_err current = .None)
    (program : current.program = entry.program) :
    SszArm.Measure.Returned entry (restored site current) := by
  refine ⟨?_, (restored_error site current).trans error,
    (restored_program site current).trans program, ?_, ?_, ?_⟩
  · simp only [restored, restoreOps, Activation.block, List.foldl,
      Activation.Op.effect, next, put, restore, state_simp_rules]
    rw [ready.stack, ready.link]
  · simp only [restored, restoreOps, Activation.block, List.foldl,
      Activation.Op.effect, next, put, restore, state_simp_rules]
    rw [ready.stack]
    simp only [bodySP, BitVec.sub_add_cancel]
  · intro reg low high
    have notStack : reg ≠ 31#5 := by bv_omega
    by_cases nineteen : reg = 19#5
    · subst reg
      simp only [restored, restoreOps, Activation.block, List.foldl, Activation.Op.effect,
        next, put, restore, state_simp_rules, BitVec.add_assoc]
      rw [ready.stack, ready.nineteen]
    by_cases twenty : reg = 20#5
    · subst reg
      simp only [restored, restoreOps, Activation.block, List.foldl, Activation.Op.effect,
        next, put, restore, state_simp_rules]
      rw [ready.stack, ready.twenty]
    by_cases link : reg = 30#5
    · subst reg
      simp only [restored, restoreOps, Activation.block, List.foldl, Activation.Op.effect,
        next, put, restore, state_simp_rules]
      rw [ready.stack, ready.link]
    simpa [restored, restoreOps, Activation.block, Activation.Op.effect,
      next, put, restore, state_simp_rules, nineteen, twenty, link, notStack] using
      ready.untouched reg low high nineteen twenty link
  · intro reg low high
    simpa using ready.vectors reg low high

end SszArm.Codec.Measure.Singleton
