import SszArm.IndicesStorage

namespace SszArm.Indices.Storage

open SszNative.Indices (Error NatSlice)
open SszArm.Codec.Storage (Image)

/-- Unit success leaves every inactive payload byte unobserved. -/
def unitResult (address : Nat) : Except Error Unit → Image
  | .ok () => .word (address + 64) 4 0
  | .error failure => error address failure

/-- The returned frontier keeps the exact committed pointer, including the
alignment-valued dangling pointer for an empty result. -/
def sliceResult (address : Nat) : Except Error NatSlice → Image
  | .ok frontier =>
      .word address 8 frontier.reservation.pointer ⋏
      .word (address + 8) 8 frontier.values.length ⋏
      operands frontier.reservation.pointer frontier.values ⋏
      .word (address + 64) 4 0
  | .error failure => error address failure

theorem unitResult_ok {protect s address}
    (stored : (unitResult address (.ok ())).Holds protect s) :
    SszArm.UintCodec.widthLoad s (address + 64) 4 = some 0 := stored.2.2

theorem sliceResult_pointer {protect s address frontier}
    (stored : (sliceResult address (.ok frontier)).Holds protect s) :
    SszArm.UintCodec.widthLoad s address 8 = some frontier.reservation.pointer := stored.1.2.2

theorem sliceResult_length {protect s address frontier}
    (stored : (sliceResult address (.ok frontier)).Holds protect s) :
    SszArm.UintCodec.widthLoad s (address + 8) 8 = some frontier.values.length := stored.2.1.2.2

theorem sliceResult_operands {protect s address frontier}
    (stored : (sliceResult address (.ok frontier)).Holds protect s) :
    (operands frontier.reservation.pointer frontier.values).Holds protect s := stored.2.2.1

theorem sliceResult_status {protect s address frontier}
    (stored : (sliceResult address (.ok frontier)).Holds protect s) :
    SszArm.UintCodec.widthLoad s (address + 64) 4 = some 0 := stored.2.2.2.2.2

end SszArm.Indices.Storage
