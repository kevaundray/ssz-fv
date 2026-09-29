import SszArm.CodecLinkedSerialize
import SszArm.CodecLinkedMeasure
import SszArm.CodecLinkedEmit
import SszArm.CodecLinkedDeserialize
import SszArm.CodecLinkedMeasureParts
import SszArm.CodecLinkedMeasureChild
import SszArm.CodecLinkedEmitParts
import SszArm.CodecLinkedIsFixed
import SszArm.CodecLinkedMeasureFixed
import SszArm.CodecLinkedDecodeFixed
import SszArm.CodecLinkedDecodeOffsets
import SszArm.CodecLinkedDecodeList
import SszArm.CodecLinkedReadOffset
import SszArm.CodecLinkedBounded
import SszArm.CodecLinkedNatCmpUsize
import SszArm.CodecLinkedPlanSingleton
import SszArm.CodecLinkedDecodeStructValues
import SszArm.SerializeImpl
import SszArm.DispatchImpl
import SszArm.ByteViewImpl
import SszArm.BitVectorCalls
import SszArm.BitListProofs
import SszArm.NatMulCalls

namespace SszArm.Codec.Linked

/-- One linked program image. The bias is added to actual ELF addresses, not
relative to an arbitrarily chosen helper. Every field constrains only immutable
instruction memory. Legacy selected-body fields repeat byte facts intentionally:
this gives constant-size projections to immutable existing execution providers. -/
structure CodeAt (s : ArmState) (loadBias : BitVec 64) : Prop where
  serialize : Serialize.CodeAt s (loadBias + 2328536#64)
  measure : Measure.CodeAt s (loadBias + 2290428#64)
  emit : Emit.CodeAt s (loadBias + 2294780#64)
  deserialize : Deserialize.CodeAt s (loadBias + 2309536#64)
  measure_parts : MeasureParts.CodeAt s (loadBias + 2298172#64)
  measure_child : MeasureChild.CodeAt s (loadBias + 2300248#64)
  emit_parts : EmitParts.CodeAt s (loadBias + 2296776#64)
  is_fixed : IsFixed.CodeAt s (loadBias + 2297968#64)
  measure_fixed : MeasureFixed.CodeAt s (loadBias + 2321108#64)
  decode_fixed : DecodeFixed.CodeAt s (loadBias + 2321936#64)
  decode_offsets : DecodeOffsets.CodeAt s (loadBias + 2322732#64)
  decode_list : DecodeList.CodeAt s (loadBias + 2324240#64)
  read_offset : ReadOffset.CodeAt s (loadBias + 2322624#64)
  bounded : Bounded.CodeAt s (loadBias + 2328284#64)
  nat_cmp_usize : NatCmpUsize.CodeAt s (loadBias + 2274508#64)
  plan_singleton : PlanSingleton.CodeAt s (loadBias + 2299872#64)
  decode_struct_values : DecodeStructValues.CodeAt s (loadBias + 2327644#64)
  legacySerialize : SszArm.Serialize.CodeAt s (loadBias + 2328536#64)
  dispatch : SszArm.Dispatch.CodeAt s (loadBias + 2309536#64)
  byteView : SszArm.ByteView.CodeAt s (loadBias + 2309536#64)
  boolBody : SszArm.BoolCodec.CodeAt s (loadBias + 2309536#64)
  uintBody : SszArm.UintCodec.CodeAt s (loadBias + 2309536#64)
  bitVector : SszArm.BitVector.JointCodeAt s (loadBias + 2309536#64)
  bitList : SszArm.BitList.JointCodeAt s (loadBias + 2309536#64)
  compare : SszArm.NatCompare.CodeAt s (loadBias + 2250156#64)
  fromU128 : SszArm.NatFromU128.CodeAt s (loadBias + 2274680#64)
  add : SszArm.NatAdd.CodeAt s (loadBias + 2242604#64)
  division : SszArm.NatDivision.JointCodeAt s (loadBias + 2231448#64)
  mul : SszArm.NatMul.JointCodeAt s (loadBias + 2246780#64)
  mulWord : SszArm.NatMulWord.CodeAt s (loadBias + 2248324#64)
  exactLeaf : SszArm.NatExact.CodeAt s (loadBias + 2326964#64)
  toU128 : SszArm.NatToU128.CodeAt s (loadBias + 2327260#64)
  delimited : SszArm.Delimited.CodeAt s (loadBias + 2320096#64)
  memcpy : SszArm.CodeAt s (loadBias + 2413776#64) SszArm.Memcpy.program

/-- The existing primitive measurement provider uses the same linked entry. -/
theorem CodeAt.legacyMeasure {s : ArmState} {bias : BitVec 64}
    (code : CodeAt s bias) : SszArm.Measure.CodeAt s (bias + 2290428#64) := by
  simpa only [SszArm.Serialize.measureOffset, BitVec.add_assoc,
    show 2328536#64 + -38108#64 = 2290428#64 by decide]
    using code.legacySerialize.measure

/-- The existing primitive emitter provider remains available unchanged. -/
theorem CodeAt.legacyEmit {s : ArmState} {bias : BitVec 64}
    (code : CodeAt s bias) : SszArm.Emit.CodeAt s (bias + 2294780#64) := by
  simpa only [SszArm.Serialize.emitOffset, BitVec.add_assoc,
    show 2328536#64 + -33756#64 = 2294780#64 by decide]
    using code.legacySerialize.emit

/-- Actual panic entry addresses. They are not replaced by returning stubs;
callers must exclude the corresponding blocks using their data invariants. -/
def panicAddresses : List Nat := [2220352, 2220400, 2221692]

/-- Each pair is an actual panic BL address and its linked target address.
The word remains in its complete function's program even on excluded paths. -/
def panicCalls : List (Nat × Nat) := [
  (2296704, 2220352),
  (2296720, 2220352),
  (2296736, 2220352),
  (2296748, 2220400),
  (2296760, 2220400),
  (2296772, 2220400),
  (2319424, 2220400),
  (2319436, 2220400),
  (2319448, 2220400),
  (2319460, 2220400),
  (2319472, 2220400),
  (2300828, 2220400),
  (2300840, 2220400),
  (2297908, 2220352),
  (2297924, 2220352),
  (2297940, 2220352),
  (2297952, 2220400),
  (2297964, 2220400),
  (2322620, 2220352),
  (2324076, 2220352),
  (2324092, 2220400),
  (2324108, 2220400),
  (2324124, 2220400),
  (2324140, 2220400),
  (2324152, 2220400),
  (2324164, 2220400),
  (2324176, 2220400),
  (2324188, 2220400),
  (2324200, 2220400),
  (2324212, 2220400),
  (2324224, 2220400),
  (2324236, 2220400),
  (2326960, 2221692),
  (2322700, 2220400),
  (2322708, 2220400),
  (2322720, 2220400),
  (2322728, 2220400),
  (2328256, 2220352),
  (2328268, 2220400),
  (2328280, 2220400)
]

end SszArm.Codec.Linked
