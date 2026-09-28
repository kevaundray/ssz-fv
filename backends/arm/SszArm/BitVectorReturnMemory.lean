import SszArm.BitVectorReturn

namespace SszArm.BitVector

open BoolCodec
open Delimited (Protected MemoryFrame)

/-- Saved caller words are protected from body writes, nested helper frames,
both reservations, and the arena cursor. -/
theorem activation_of_memory {s t : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data)
    (saved : Protected (writesFor s (outcome s length data))
      ((r (.GPR 31#5) s).toNat + 272) 96)
    (frame : MemoryFrame (writesFor s (outcome s length data)) s t) :
    BoolCodec.ActivationPreserved s t := by
  intro index within
  change t.mem _ = s.mem _
  apply frame.protected_byte saved
  · have bound := owned.stackHigh
    bv_omega
  · have bound := owned.stackHigh
    bv_omega

/-- The shared epilogue summary restores the physical saved values. No false
identification of entry X19--X28 with the caller's callee-saved values is used. -/
theorem returned_of_activation (s t : ArmState)
    (sp : r (.GPR 31#5) t = r (.GPR 31#5) s)
    (error : read_err t = .None) (activation : BoolCodec.ActivationPreserved s t)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64) :
    Returned s (BoolCodec.returned t) := by
  refine ⟨BoolCodec.returned_pc_of_activation s t sp activation, ?_, ?_, ?_, ?_, ?_⟩
  · simpa (config := {decide := true}) [BoolCodec.returned, state_simp_rules] using error
  · rw [BoolCodec.returned_sp, sp]
  · intro reg offset member
    have bounds := BoolCodec.savedRegister_bounds reg offset member
    rw [BoolCodec.returned_register t reg offset member, sp]
    have memory : read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset)
        (BoolCodec.returned t) =
        read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) t := by
      simp only [BoolCodec.returned, state_simp_rules]
    rw [memory]
    have word := BoolCodec.activation_word s t (offset - 272) activation (by omega)
    change read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) t =
      read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) s
    change read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 (272 + (offset - 272))) t =
      read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 (272 + (offset - 272))) s at word
    simpa only [show 272 + (offset - 272) = offset by omega] using word
  · intro reg low high
    simpa (config := {decide := true}) [BoolCodec.returned, state_simp_rules] using vectors reg low high
  · intro index within
    simpa only [read_mem, BoolCodec.returned_mem] using activation index within

/-- All observed result/resource bytes survive the actual common return. -/
theorem return_observe (s : ArmState) : UintCodec.widthLoad (BoolCodec.returned s) =
    UintCodec.widthLoad s := by
  funext address bytes
  simp only [UintCodec.widthLoad, BoolCodec.returned, state_simp_rules]

end SszArm.BitVector
