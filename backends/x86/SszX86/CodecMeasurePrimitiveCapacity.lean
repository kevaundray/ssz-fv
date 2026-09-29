import SszX86.CodecMeasurePrimitiveCursor

set_option autoImplicit false

namespace SszX86.CodecMeasure.Geometry
open SszNative

/-- Primitive measurement respects the cursor bound without a successful outcome
or positive/nonempty arena premise. -/
theorem primitive_capacity (shape : Serialize.Desc) (value : SszNative.Codec.Value)
    (arena : Delimited.ArenaState) (initial : arena.used ≤ arena.capacity) :
    (SszNative.CodecMeasure.primitive shape value arena).used ≤ arena.capacity :=
  SszX86.CodecMeasure.primitive_used_bound shape value.toPrimitive arena initial

end SszX86.CodecMeasure.Geometry
