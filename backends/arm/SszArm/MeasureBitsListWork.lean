import SszArm.MeasureBitsListLoad
import SszArm.MeasureOwnership

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Desc Packed)

inductive Schema where
  | bounded (cap : NatOperand)
  | progressive (cap : Option NatOperand)

def Schema.descriptor : Schema → Desc
  | .bounded cap => .bitList cap
  | .progressive cap => .progressiveBitList cap

def Schema.cap : Schema → Option NatOperand
  | .bounded cap => some cap
  | .progressive cap => cap

def Schema.kind : Schema → ListEntry.Kind
  | .bounded _ => .bounded
  | .progressive _ => .progressive

structure Work (s : ArmState) (args : Args) (schema : Schema) (bits : Packed) : Prop where
  result : r (.GPR 19#5) s = args.result
  arena : r (.GPR 20#5) s = args.arena
  stack : r (.GPR 31#5) s = args.bodySP
  low : r (.GPR 26#5) s = bits.count.setWidth 64
  high : r (.GPR 25#5) s = (bits.count >>> (64 : Nat)).setWidth 64
  cap : match schema.cap with
    | none => True
    | some operand => r (.GPR 22#5) s = operand.pointer ∧ r (.GPR 23#5) s = operand.payload
  flag : match schema with
    | .bounded _ => True
    | .progressive cap => r (.GPR 8#5) s = if cap.isSome then 1#64 else 0#64

theorem list_outcome (s : ArmState) (args : Args) (schema : Schema) (bits : Packed) :
    Measure.outcome s args schema.descriptor (.bits bits) =
      SszNative.Serialize.measureList schema.cap bits (arenaOf s args) := by
  cases schema <;> rfl

end SszArm.Measure.Bits.List
