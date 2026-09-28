import SszArm.DispatchBitListOwned

namespace SszArm.DispatchBitList

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame NatOwned)
open Dispatch (bodySP entered)
open BitList (Variant optionAddress)

theorem returned_of_body {s t : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (returned : BitList.Returned (entered s (dispatchKind kind)) t) :
    Returned s t := by
  have low : 368 ≤ (r (.GPR 31#5) s).toNat := by have := owned.stackLow; omega
  refine ⟨?_, returned.error, ?_, ?_, ?_⟩
  · have original := Dispatch.entered_saved s (dispatchKind kind) low 30#5 280
      (by simp [BoolCodec.savedRegisters])
    have pc := returned.pc
    rw [Dispatch.entered_sp] at pc
    exact pc.trans original
  · have stack := returned.sp
    simp only [Dispatch.entered_sp, bodySP] at stack
    bv_omega
  · intro reg offset member
    have saved := Dispatch.entered_saved s (dispatchKind kind) low reg offset member
    have restored := returned.registers reg offset member
    rw [Dispatch.entered_sp] at restored
    exact restored.trans saved
  · intro reg low high
    simpa only [Dispatch.entered_vector] using returned.vectors reg low high

theorem activation_word_at (u t : ArmState) (sp : BitVec 64)
    (stack : r (.GPR 31#5) u = sp) (offset : Nat)
    (bounds : 272 ≤ offset ∧ offset + 8 ≤ 368)
    (preserved : BoolCodec.ActivationPreserved u t) :
    read_mem_bytes 8 (sp + BitVec.ofNat 64 offset) t =
      read_mem_bytes 8 (sp + BitVec.ofNat 64 offset) u := by
  have slot : 272 + (offset - 272) = offset := by omega
  have word := BoolCodec.activation_word u t (offset - 272) preserved (by omega)
  have address := (congrArg (fun p => p + BitVec.ofNat 64 (272 + (offset - 272))) stack).trans
    (congrArg (fun n => sp + BitVec.ofNat 64 n) slot)
  exact (congrArg (fun a => read_mem_bytes 8 a t) address).symm.trans
    (word.trans (congrArg (fun a => read_mem_bytes 8 a u) address))

/-- Compose the prologue frame with the exact accepted native body post. -/
theorem post_of_body {s t : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (post : BitList.Post (entered s (dispatchKind kind)) t kind limit data) :
    Post s t kind limit data := by
  have bodyFrame : MemoryFrame (bodyWrites s kind (outcome s limit data).allocation)
      (entered s (dispatchKind kind)) t := by
    simpa only [entered_outcome owned, entered_writes] using post.frame
  have frame := ((save_covered s kind _).frame (entry_frame owned)).trans
    ((body_covered s kind _).frame bodyFrame)
  have allocation := (SszNative.Delimited.run_resources limit data (arenaOf s) (body_owned owned).physical).1
  have physicalFrame : MemoryFrame (writesFor s kind (SszNative.Delimited.allocation data (arenaOf s))) s t := by
    simpa only [outcome, allocation] using frame
  refine ⟨returned_of_body owned post.returned, ?_, ?_, ?_, ?_, ?_, frame,
    physicalFrame.bytes _ _ owned.inputBound owned.inputOwned owned.input, ?_, ?_, ?_, ?_⟩
  · simpa (config := {decide := true}) only [Dispatch.entered_reg, entered_option,
      entered_outcome owned] using post.result
  · simpa only [entered_outcome owned] using post.prepared
  · simpa only [Dispatch.entered_arena, entered_outcome owned] using post.cursor
  · have before := arena_read owned 0 8 (by decide)
    simp only [BitVec.add_zero] at before
    have restored := post.arenaBase
    rw [Dispatch.entered_arena] at restored
    exact restored.trans before
  · have restored := post.arenaCapacity
    rw [Dispatch.entered_arena] at restored
    exact restored.trans (arena_read owned 8 8 (by decide))
  · intro address low high
    exact physicalFrame.protected_byte owned.inputOwned address low high
  · intro address low high
    exact physicalFrame.protected_byte owned.descriptorOwned address low high
  · intro cap capEq address
    dsimp only
    intro nonzero low high
    have countNonzero : read_mem_bytes 8 (optionAddress s kind + 16#64) s ≠ 0#64 := by
      intro zero
      simp only [zero, BitVec.toNat_ofNat] at high
      omega
    exact physicalFrame.protected_byte (owned.limbsOwned cap capEq nonzero countNonzero) address low high
  · intro kindEq reg offset member
    have bounds := BoolCodec.savedRegister_bounds reg offset member
    have word := activation_word_at (entered s (dispatchKind kind)) t (bodySP s)
      (Dispatch.entered_sp s (dispatchKind kind)) offset bounds (post.activation kindEq)
    exact word.trans (Dispatch.entered_saved s (dispatchKind kind)
      (by have := owned.stackLow; omega) reg offset member)

end SszArm.DispatchBitList
