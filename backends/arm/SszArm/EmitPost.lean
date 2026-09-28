import SszArm.EmitObservations

namespace SszArm.Emit

open SszNative.Serialize (Desc Value)
open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- Original borrowed headers, padded limbs, backing bytes and spare output
follow from the physical write frame; they are not future-state hypotheses. -/
theorem post_of_return (s t : ArmState) (desc : Desc) (value : Value) (size : Nat)
    (owned : Owned s (Args.ofEntry s) desc value size)
    (returned : Returned s t)
    (length : read_mem_bytes 8 (Args.ofEntry s).result t = BitVec.ofNat 64 size)
    (status : read_mem_bytes 4 ((Args.ofEntry s).result + 64#64) t = 0#32)
    (bytes : SszNative.ByteView.BytesAt (widthLoad t) (Args.ofEntry s).output.toNat
      (SszNative.Serialize.emit desc value))
    (frame : MemoryFrame (writesFor (Args.ofEntry s) size) s t) : Post s t desc value size := by
  refine ⟨returned, length, status, bytes, frame,
    descriptor_preserved owned frame, value_preserved owned frame, ?_, ?_, ?_, ?_, ?_⟩
  · exact frame.read _ _ owned.descriptorBound owned.descriptorOwned
  · exact frame.read _ _ owned.valueBound owned.valueOwned
  · intro operand member
    exact NatDivision.operand_preserved frame operand (owned.operand_at operand member)
      (owned.operandOwned operand member)
  · intro span member address low high
    exact frame.protected_byte (owned.backingOwned span member) address low high
  · intro index low high
    exact output_tail owned frame index low high

/-- Success writes agree with the accepted pure emitter and the pinned encoding.
The equality does not assert that unused result bytes are initialized. -/
theorem Post.encoding {s t : ArmState} {desc : Desc} {value : Value} {size : Nat}
    (post : Post s t desc value size)
    (expected : SszNative.Serialize.expectedSize desc value = .ok size) :
    ∃ bytes, Ssz.serialize desc.erase value.erase = .ok bytes ∧ bytes.size = size ∧
      SszNative.ByteView.BytesAt (widthLoad t) (Args.ofEntry s).output.toNat bytes ∧
      read_mem_bytes 8 (Args.ofEntry s).result t = BitVec.ofNat 64 bytes.size ∧
      read_mem_bytes 4 ((Args.ofEntry s).result + 64#64) t = 0#32 := by
  obtain ⟨encoding, width⟩ := SszNative.Serialize.expected_encoding desc value
  have exactSize := width size expected
  refine ⟨SszNative.Serialize.emit desc value, ?_, exactSize, post.bytes, ?_, post.status⟩
  · simpa only [expected, Except.map] using encoding
  · simpa only [exactSize] using post.length

end SszArm.Emit
