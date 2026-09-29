import SszArm.CodecEmitContract
import SszArm.CodecSerializeContract

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure (Plan)
open UintCodec (widthLoad)

 theorem byteMemory_widthLoad (s : ArmState) (address : Nat) :
    (Emit.byteMemory s address).map UInt8.toNat = widthLoad s address 1 := by
  rfl

 theorem byteMemory_observed {s : ArmState} {address : Nat} {byte : UInt8}
    (observed : Emit.byteMemory s address = some byte) :
    widthLoad s address 1 = some byte.toNat := by
  have same := congrArg (Option.map UInt8.toNat) observed
  simpa only [byteMemory_widthLoad, Option.map_some] using same

 theorem byteMemory_unchanged {s t : ArmState} {address : Nat}
    (unchanged : Emit.byteMemory t address = Emit.byteMemory s address) :
    t.mem (BitVec.ofNat 64 address) = s.mem (BitVec.ofNat 64 address) := by
  have observed := congrArg (Option.map UInt8.toNat) unchanged
  simp only [byteMemory_widthLoad, widthLoad, Option.some.injEq] at observed
  have same : read_mem_bytes 1 (BitVec.ofNat 64 address) t =
      read_mem_bytes 1 (BitVec.ofNat 64 address) s := BitVec.eq_of_toNat_eq observed
  simpa only [BoolCodec.read_one, read_mem, read_store] using same

/-- Exact initialized output follows from actual emitter execution plus the
measured plan's pinned semantic correspondence; no old output contents occur. -/
theorem emitted_bytes {s t : ArmState} {desc : Desc} {value : Value}
    {retain : Bool} {plan : Plan} {supplied : Option Plan}
    (post : Emit.Post s t desc value plan supplied)
    (owned : Emit.Owned s (Emit.Args.ofEntry s) desc value retain plan supplied)
    (bytes : Ssz.Bytes) (semantic : Ssz.serialize desc.erase value.erase = .ok bytes)
    (size : bytes.size = plan.size.value) :
    SszNative.ByteView.BytesAt (widthLoad t) (Emit.Args.ofEntry s).output.toNat bytes := by
  intro index inside
  have initialized := post.initialized owned bytes semantic index inside size
  have observed := byteMemory_observed initialized
  simpa only [Array.getElem?_eq_getElem inside, Option.getD_some] using observed

/-- The emitter's exact shared write semantics preserves every physical suffix
byte, even for zero-size encodings and initially uninitialized output memory. -/
theorem emitted_suffix {s t : ArmState} {desc : Desc} {value : Value}
    {plan : Plan} {supplied : Option Plan} (post : Emit.Post s t desc value plan supplied)
    (bytes : Ssz.Bytes) (encoded : SszNative.CodecEmit.Encodes
      (SszNative.CodecEmit.emit desc value supplied (Emit.Args.ofEntry s).out).writes
      (Emit.Args.ofEntry s).output.toNat bytes)
    (index : Nat) (outside : bytes.size ≤ index)
    (inside : index < (Emit.Args.ofEntry s).capacity.toNat) :
    t.mem ((Emit.Args.ofEntry s).output + BitVec.ofNat 64 index) =
      s.mem ((Emit.Args.ofEntry s).output + BitVec.ofNat 64 index) := by
  have unchanged := byteMemory_unchanged (post.suffix bytes encoded index outside inside)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using unchanged

end SszArm.Codec.Serialize
