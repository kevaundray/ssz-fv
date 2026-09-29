import SszX86.CodecSerializeMemory
import SszX86.CodecStoragePlan

namespace SszX86.CodecSerialize.Publish
open SszNative UintCodec
open SszX86.Serialize.Publish

private theorem image_root_same (before after : DataMem) (p : BitVec 64) (image : Image)
    (source : ImageAt before p image) (destination : ImageAt after p image) :
    Codec.PlanRootSame before after p := by
  refine ⟨?_, destination.w1.trans source.w1.symm, ?_, ?_,
    destination.w4.trans source.w4.symm⟩
  · simpa only [BitVec.add_zero] using destination.w0.trans source.w0.symm
  · unfold widthLoad
    simp only [BitVec.ofNat_toNat]
    exact congrArg (Option.map Int.toNat) (destination.w2.trans source.w2.symm)
  · unfold widthLoad
    rw [width_address]
    have address : p + 16 + BitVec.ofNat 64 8 = p + 24 := by bv_omega
    rw [address]
    exact congrArg (Option.map Int.toNat) (destination.w3.trans source.w3.symm)

/-- The real PC161..191 repack preserves the whole retained Plan graph, not only
its size. The outer header may lie in mutable stack scratch; only actual child
headers and borrowed size limbs need exclusion from the write footprint. -/
theorem prepared_plan (s : MachineData) (image : Image) (flags : StatusFlags)
    (plan : SszNative.CodecMeasure.Plan) (readable : Codec.Footprint)
    (bound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (source : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) image)
    (stored : Codec.PlanAt s.dmem readable (s.regs.rsp.toBitVec + 24#64) plan)
    (safe : ∀ a, Codec.planBorrowed plan a →
      ¬ Emit.InSpan a (s.regs.rsp.toBitVec + 8#64) 56) :
    Codec.PlanAt (prepared s image flags).dmem readable
      (s.regs.rsp.toBitVec + 24#64) plan := by
  apply Codec.PlanAt.replaceRoot stored
  · exact image_root_same _ _ _ image source
      (prepared_state_image s image flags bound source)
  · exact prepared_state_frame s image flags
  · exact safe

end SszX86.CodecSerialize.Publish
