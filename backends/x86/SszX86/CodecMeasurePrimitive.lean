import SszX86.CodecMeasurePrimitiveBinding
import SszX86.CodecMeasureCore
import SszX86.MeasureProofs

set_option autoImplicit false

namespace SszX86.CodecMeasure
open SszNative

/-- The complete linked measure image executes each primitive constructor using
its existing proved native path. Both retain values and all wrong-kind recursive
Value roots are admitted. This is a base case, not a compound-call assumption. -/
theorem primitive_correct (e : Executable) (base : Int64) (code : CodeAt e base)
    (helpers : Measure.HelpersAt e base) (s : MachineData)
    (shape : Serialize.Desc) (value : SszNative.Codec.Value)
    (buffer address capacity used ra : BitVec 64) (retain : Bool)
    (owned : Measure.Owned s base shape value.toPrimitive
      buffer address capacity used ra retain) :
    Eventually (step e) (fun final =>
      Measure.Post s shape value.toPrimitive buffer address capacity used ra final ∧
      ResultAt (UintCodec.widthLoad final.1.dmem) s.regs.rdi.toNat
        (SszNative.CodecMeasure.measure (.primitive shape) value
          (Measure.arenaState address capacity used) retain).result ∧
      UintCodec.widthLoad final.1.dmem (s.regs.rcx.toNat + 16) 8 =
        some (SszNative.CodecMeasure.measure (.primitive shape) value
          (Measure.arenaState address capacity used) retain).used) (s, base) := by
  apply eventually_weaken (step e) _ _ _ _
    (Measure.program_correct e base code.primitive helpers s shape value.toPrimitive
      buffer address capacity used ra retain owned)
  intro final post
  have model : SszNative.CodecMeasure.measure (.primitive shape) value
      (Measure.arenaState address capacity used) retain =
      SszNative.CodecMeasure.primitive shape value (Measure.arenaState address capacity used) := by
    rw [SszNative.CodecMeasure.measure]
    rfl
  refine ⟨post, ?_, ?_⟩
  · rw [model]
    exact (primitive_resultAt _ _ _).mpr post.observed
  · simpa only [model, SszNative.CodecMeasure.primitive] using post.cursor

end SszX86.CodecMeasure
