import SszX86.HashCombineCopy
import SszX86.HashStateUpdate

namespace SszX86.Hash.Combine
open SszNative.HashStream

/-- The CALL slot is disjoint from every byte of the in-place native state. -/
theorem call_state_preserved (s : MachineData) (ra : BitVec 64) (state : Model)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state) :
    StateAt (callState s ra).dmem (s.regs.rsp.toBitVec + 8) state := by
  apply bytesAt_frame _ _ _ _ _ stored (storeInt_frame _ _ _ _)
  intro i hi inside
  have hi' : i < 112 := by simpa only [Vector.length_toList] using hi
  rcases inside with ⟨j, hj, equal⟩
  bv_omega

/-- The copied interval, including a zero-length interval, updates the model's
exact buffer while all stale bytes and all other fields remain unchanged. -/
theorem copied_state (s : MachineData) (ra : BitVec 64) (state : Model)
    (input : ByteArray) (src dst count : Nat)
    (hd : dst + count ≤ 64) (hs : src + count ≤ input.size)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (physical : Physical (s.regs.rsp.toBitVec + 8) 112)
    (destination : s.regs.rdi.toBitVec = (s.regs.rsp.toBitVec + 8) + BitVec.ofNat 64 dst)
    (t : MachineState)
    (post : Hash.CopyPost s ra ((input.data.toList.drop src).take count) t) :
    StateAt t.1.dmem (s.regs.rsp.toBitVec + 8)
      {state with buffer := copy state.buffer dst input src count hd hs} := by
  have length : ((input.data.toList.drop src).take count).length = count := by
    simp only [List.length_take, List.length_drop, Array.length_toList, ByteArray.size_data]
    omega
  have before := call_state_preserved s ra state stored
  have bufferPhysical : Physical (s.regs.rsp.toBitVec + 8) 64 := by
    unfold Physical at physical ⊢
    omega
  have written := bytesAt_copy (callState s ra).dmem t.1.dmem
    (s.regs.rsp.toBitVec + 8) state.buffer dst input src count hd hs bufferPhysical
    (stateAt_buffer _ _ _ before)
    (by simpa only [destination] using post.output)
    (by simpa only [destination, length] using post.callFrame)
  apply stateAt_replace_buffer s.dmem t.1.dmem (s.regs.rsp.toBitVec + 8) state
    _ (fun a => InSpan a (s.regs.rsp.toBitVec - 8) 8) physical stored written
  · apply frame_mono _ _ _ _ post.frame
    intro a inside
    rcases inside with ⟨i, hi, equal⟩ | slot
    · left
      refine ⟨dst + i, by rw [length] at hi; omega, ?_⟩
      rw [equal, destination, memmove_addr_add]
    · exact Or.inr slot
  · intro i hi inside
    rcases inside with ⟨j, hj, equal⟩
    bv_omega

/-- Copying a buffer interval and its return slot fits the same bounded frame
as a compression iteration. -/
theorem copy_frame_drain (s : MachineData) (ra : BitVec 64) (bytes : List UInt8)
    (dst : Nat) (bound : dst + bytes.length ≤ 64)
    (destination : s.regs.rdi.toBitVec = (s.regs.rsp.toBitVec + 8) + BitVec.ofNat 64 dst)
    (t : MachineState) (post : Hash.CopyPost s ra bytes t) :
    MemoryFrame s.dmem t.1.dmem (DrainWritable s.regs.rsp.toBitVec) := by
  apply frame_mono _ _ _ _ post.frame
  intro a inside
  rcases inside with ⟨i, hi, equal⟩ | ⟨i, hi, equal⟩
  · left
    refine ⟨dst + i, by omega, ?_⟩
    rw [equal, destination, memmove_addr_add]
  · right
    refine ⟨160 + i, by omega, ?_⟩
    rw [equal]
    bv_omega

end SszX86.Hash.Combine
