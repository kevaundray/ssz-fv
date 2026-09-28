import SszArm.SerializePostObservations
import SszArm.SerializePostFrame
import SszArm.SerializePostRefinement

namespace SszArm.Serialize

open SszNative.Serialize (Desc Value)
open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- The complete wrapper contract follows from the executed return observations
and exact actual-write frame. Original input preservation and the capacity tail
are conclusions, not future-state premises of ownership. The frame is retained
without widening, so untouched Result padding remains part of the guarantee. -/
theorem post_of_return (s t : ArmState) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value)
    (returned : Emit.Returned s t)
    (result : ResultAt (widthLoad t) (Args.ofEntry s).result.toNat
      (outcome s (Args.ofEntry s) desc value).outcome.result)
    (cursor : (read_mem_bytes 8 ((Args.ofEntry s).arena + 16#64) t).toNat =
      (outcome s (Args.ofEntry s) desc value).outcome.used)
    (header : read_mem_bytes 8 (Args.ofEntry s).arena t = read_mem_bytes 8 (Args.ofEntry s).arena s ∧
      read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) t =
        read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) s)
    (written : ∀ call ∈ (outcome s (Args.ofEntry s) desc value).outcome.calls,
      NatDivision.WrittenAt (widthLoad t) call)
    (bytes : SszNative.ByteView.BytesAt (widthLoad t) (Args.ofEntry s).output.toNat
      (outcome s (Args.ofEntry s) desc value).writes)
    (frame : MemoryFrame (writesFor s (Args.ofEntry s) desc value) s t) :
    Post s t desc value := by
  have observations := frame_of_covers frame (writesFor_covered owned)
  refine ⟨returned, result, cursor, header, written, bytes, frame,
    descriptor_preserved owned observations, value_preserved owned observations, ?_, ?_, ?_⟩
  · intro operand member
    exact NatDivision.operand_preserved observations operand (owned.operand_at operand member)
      (owned.operandOwned operand member)
  · intro span member address low high
    exact observations.protected_byte (owned.backingOwned span member) address low high
  · intro index low high
    exact output_tail owned frame index low high

end SszArm.Serialize
