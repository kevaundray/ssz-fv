import SszX86.CodecEmitPrimitiveOwned
import SszX86.CodecEmitMemory
import SszX86.EmitProofs

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative

/-- Complete entry-to-RET execution of the seven primitive branches of the
linked emitter, with the shared recursive ordered-write trace. All premises
concern original machine storage and the past generated-plan invariant. -/
theorem primitive_program_correct (e : Executable) (base : Int64)
    (code : Emit.CodeAt e base) (copy : Emit.MemcpyCodeAt e (base + 110736))
    (s : MachineData) (shape : Serialize.Desc) (value : SszNative.Codec.Value)
    (supplied : Option SszNative.CodecMeasure.Plan) (r : SszX86.Codec.Footprint)
    (ra : BitVec 64) (call : GeneratedCall (.primitive shape) value supplied s.regs.r9.toNat)
    (memory : PrimitiveMemory s base shape value r ra call.measured.size.value) :
    Eventually (Emit.step e) (fun final =>
      (∃ buffer, Emit.Post s shape value.toPrimitive buffer ra call.measured.size.value final) ∧
      OutputAt s.dmem final.1.dmem s.regs.r8.toBitVec s.regs.r9.toNat
        (SszNative.CodecEmit.emit (.primitive shape) value supplied
          ⟨s.regs.r8.toNat, s.regs.r9.toNat⟩).writes ∧
      SszX86.Codec.DescAt final.1.dmem r s.regs.rsi.toBitVec (.primitive shape) ∧
      SszX86.Codec.ValueAt final.1.dmem r s.regs.rdx.toBitVec value)
      (s, base) := by
  obtain ⟨buffer, owned⟩ := PrimitiveMemory.owned call memory
  apply eventually_weaken (Emit.step e) _ _ _ _
    (Emit.program_correct e base code copy s shape value.toPrimitive buffer ra
      call.measured.size.value owned)
  intro final post
  have semantic : Ssz.serialize (SszNative.Codec.Desc.primitive shape).erase value.erase =
      .ok (Serialize.emit shape value.toPrimitive) := by
    simpa only [SszNative.Codec.Desc.erase, SszNative.Codec.Value.erase_toPrimitive]
      using owned.valid.pinned
  have encoded := call.encodes s.regs.r8.toNat (Serialize.emit shape value.toPrimitive) semantic
  refine ⟨⟨buffer, post⟩, ?_,
    memory.descriptor.frame post.memory.frame memory.readonly,
    memory.valueStored.frame post.memory.frame memory.readonly⟩
  apply OutputAt.of_bytes (by simpa only [UInt64.toNat_toBitVec] using encoded)
    post.memory.output
  intro i lower upper
  rw [post.outputFrame i upper]
  exact Serialize.applyWrites_tail _ _ i lower

end SszX86.CodecEmit
