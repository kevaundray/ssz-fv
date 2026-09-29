import SszX86.CodecEmitLeafOwned
import SszX86.CodecEmitPrimitiveBinding

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative

/-- All seven immutable primitive body providers execute against the full linked
image with the exact active result footprint. In particular this theorem does
not inherit the older entry wrapper's unnecessary 80-byte sret exclusion. -/
theorem leaf_body_correct (e : Executable) (base : Int64) (code : CodeAt e base)
    (copy : Emit.MemcpyCodeAt e (base + 110736))
    (s : MachineData) (shape : Serialize.Desc) (value : SszNative.Codec.Value)
    (supplied : Option SszNative.CodecMeasure.Plan) (r : SszX86.Codec.Footprint)
    (buffer : BitVec 64)
    (call : GeneratedCall (.primitive shape) value supplied s.regs.r9.toNat)
    (owned : LeafOwned s shape value supplied r buffer call) :
    Eventually (step e) (fun final => final.2 = base + 1593 ∧
      Emit.BodyPost s (Serialize.emit shape value.toPrimitive) final.1)
      (s, base + Int64.ofNat (Emit.bodyEntry shape)) := by
  have compatible := Emit.success_compatible shape value.toPrimitive _ call.primitive_valid.success
  cases shape <;> cases value <;>
    simp only [SszNative.Codec.Value.toPrimitive, Emit.Compatible] at compatible
  · exact Emit.bool_body e base code.primitive s _ owned.bool
  · apply eventually_weaken (step e) _ _ _ _
      (Emit.Uint.body_runs e base code.primitive s _ _ call.measured.size.value owned.uint)
    intro final post
    exact ⟨post.1, post.2.1⟩
  · simpa only [Emit.bodyEntry, SszNative.Codec.Value.toPrimitive, Serialize.emit,
      show Int64.ofNat 256 = (256 : Int64) by decide] using
      Emit.Bytes.body_runs e base code.primitive copy s _ buffer owned.bytes
  · simpa only [Emit.bodyEntry, SszNative.Codec.Value.toPrimitive, Serialize.emit,
      show Int64.ofNat 256 = (256 : Int64) by decide] using
      Emit.Bytes.body_runs e base code.primitive copy s _ buffer owned.bytes
  · exact Emit.Bits.body_correct e base code.primitive copy s _ _ buffer
      call.measured.size.value owned.bits
  · exact Emit.Bits.body_correct e base code.primitive copy s _ _ buffer
      call.measured.size.value owned.bits
  · exact Emit.Bits.body_correct e base code.primitive copy s _ _ buffer
      call.measured.size.value owned.bits

end SszX86.CodecEmit
