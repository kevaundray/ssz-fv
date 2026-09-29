import SszX86.CodecSerializePlan

namespace SszX86.CodecSerialize.Publish
open SszNative UintCodec
open SszX86.Serialize.Publish

/-- The original successful PC47 path preserves the entire retained recursive
Plan while repacking its five native header words and loading the raw size pair. -/
theorem prepare_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (image : Image) (plan : SszNative.CodecMeasure.Plan)
    (readable : Codec.Footprint)
    (stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 96)
    (bound : s.regs.rsp.toNat + 96 ≤ 2 ^ 64)
    (source : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) image)
    (result : CodecMeasure.ResultAt (widthLoad s.dmem)
      (s.regs.rsp.toBitVec + 24#64).toNat (.ok plan))
    (stored : Codec.PlanAt s.dmem readable (s.regs.rsp.toBitVec + 24#64) plan)
    (safe : ∀ a, Codec.planBorrowed plan a →
      ¬ Emit.InSpan a (s.regs.rsp.toBitVec + 8#64) 56) :
    Eventually (step e)
      (fun t => t.2 = base + 196 ∧
        CodecMeasure.ResultAt (widthLoad t.1.dmem)
          (s.regs.rsp.toBitVec + 24#64).toNat (.ok plan) ∧
        Codec.PlanAt t.1.dmem readable (s.regs.rsp.toBitVec + 24#64) plan ∧
        t.1.regs.rax.toBitVec = plan.size.pointer ∧
        t.1.regs.r9.toBitVec = plan.size.payload ∧
        Emit.MemoryFrame s.dmem t.1.dmem
          (fun a => Emit.InSpan a (s.regs.rsp.toBitVec + 8#64) 56))
      (s, base + 47) := by
  have zero := (image_plan s.dmem _ image plan source result).1
  apply Serialize.Publish.success_cps e base code.wrapper s image stack bound source zero
  intro flags
  obtain ⟨observed, pointer, payload⟩ := prepared_result s image flags plan bound source result
    (fun a borrowed => safe a (Or.inl borrowed))
  exact .refl _ ⟨rfl, observed, prepared_plan s image flags plan readable bound source stored safe,
    pointer, payload, prepared_state_frame s image flags⟩

end SszX86.CodecSerialize.Publish
