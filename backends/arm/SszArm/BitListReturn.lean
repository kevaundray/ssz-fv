import SszArm.BitListPost
import SszArm.BitVectorReturnMemory

namespace SszArm.BitList

/-- The non-tail call preserves the still-live original saved activation. -/
theorem list_returned {s t : ArmState} {base : BitVec 64} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s .list limit data) (post : Delimited.Post (called s base .list) t limit data) :
    Returned s (BoolCodec.returned t) := by
  have frame := helper_post_frame owned post rfl
  have allocation := (SszNative.Delimited.run_resources limit data (arenaOf s) owned.physical).1
  have activation := activation_from_frame owned (by simpa only [outcome, allocation] using frame)
  have sp : r (.GPR 31#5) t = r (.GPR 31#5) s := by
    simpa only [called_sp, helperSP] using post.returned.sp
  have vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64 := by
    intro reg low high
    simpa only [called_vectors] using post.returned.vectors reg low high
  have restored := BitVector.returned_of_activation s t sp post.returned.error activation vectors
  exact ⟨restored.pc, restored.error, restored.sp, restored.registers, restored.vectors⟩

/-- In the tail branch the helper preserves registers already restored by the
wrapper. Its RET uses the original caller LR and SP, not an invented BL link. -/
theorem progressive_returned {s t : ArmState} {base : BitVec 64} {limit : Option Nat} {data : Ssz.Bytes}
    (post : Delimited.Post (called s base .progressive) t limit data) : Returned s t := by
  refine ⟨?_, post.returned.error, ?_, ?_, ?_⟩
  · simpa (config := {decide := true}) [called, progressiveCalled, BoolCodec.returned,
      state_simp_rules] using post.returned.pc
  · simpa only [called_sp, helperSP] using post.returned.sp
  · intro reg displacement member
    have range : 19 ≤ reg.toNat ∧ reg.toNat ≤ 30 := by
      simp only [BoolCodec.savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    have notOne : reg ≠ 1#5 := by bv_omega
    have notFour : reg ≠ 4#5 := by bv_omega
    have preserved := post.returned.registers reg range.1 range.2
    have same : r (.GPR reg) (called s base .progressive) = r (.GPR reg) (BoolCodec.returned s) := by
      simp (config := {decide := true}) [called, progressiveCalled, state_simp_rules, notOne, notFour]
    rw [preserved, same, BoolCodec.returned_register s reg displacement member]
    simp only [BoolCodec.returned, state_simp_rules]
  · intro reg low high
    simpa only [called_vectors] using post.returned.vectors reg low high

end SszArm.BitList
