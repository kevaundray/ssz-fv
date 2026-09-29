import SszArm.SerializeSaved

namespace SszArm.Codec.Serialize

open Delimited (Span Protected MemoryFrame)
open SszArm.Serialize.Finish (sp saved returned)

/-- Actual wrapper save slots and the standard Linux AAPCS callee-saved state.
The platform register x18 is intentionally not a callee-saved requirement. -/
structure SavedFrom (original s : ArmState) : Prop where
  stack : sp s + 144#64 = sp original
  words : ∀ reg displacement, (reg, displacement) ∈ saved →
    read_mem_bytes 8 (sp s + BitVec.ofNat 64 displacement) s = r (.GPR reg) original
  registers : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 30 →
    reg ∉ [19#5, 20#5, 21#5, 22#5, 23#5, 30#5] →
    r (.GPR reg) s = r (.GPR reg) original
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) s).setWidth 64 = (r (.SFP reg) original).setWidth 64

 theorem SavedFrom.of_frame {s t u : ArmState} {writes : List Span}
    (before : SavedFrom s t) (frame : MemoryFrame writes t u)
    (stack : sp u = sp t) (physical : (sp t).toNat + 144 ≤ 2^64)
    (saveProtected : Protected writes ((sp t).toNat + 96) 48)
    (registers : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 30 →
      reg ∉ [19#5, 20#5, 21#5, 22#5, 23#5, 30#5] → r (.GPR reg) u = r (.GPR reg) t)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) u).setWidth 64 = (r (.SFP reg) t).setWidth 64) : SavedFrom s u := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stack]
    exact before.stack
  · intro reg displacement member
    have range := SszArm.Serialize.Finish.saved_bounds reg displacement member
    rw [stack]
    have address : (sp t + BitVec.ofNat 64 displacement).toNat = (sp t).toNat + displacement := by
      bv_omega
    have piece := saveProtected.subspan (displacement - 96) 8 (by omega)
    have offset : (sp t).toNat + 96 + (displacement - 96) = (sp t).toNat + displacement := by omega
    have field : Protected writes (sp t + BitVec.ofNat 64 displacement).toNat 8 := by
      simpa only [address, offset] using piece
    rw [frame.read _ 8 (by rw [address]; omega) field]
    exact before.words reg displacement member
  · intro reg lower upper outside
    exact (registers reg lower upper outside).trans (before.registers reg lower upper outside)
  · intro reg lower upper
    exact (vectors reg lower upper).trans (before.vectors reg lower upper)

 theorem returned_original (original s : ArmState) (before : SavedFrom original s)
    (error : read_err s = .None) : Delimited.Returned original (returned s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (SszArm.Serialize.Finish.returned_pc s).trans (before.words 30#5 96 (by simp [saved]))
  · exact (SszArm.Serialize.Finish.returned_error s).trans error
  · exact (SszArm.Serialize.Finish.returned_sp s).trans before.stack
  · intro reg lower upper
    by_cases member : reg ∈ [19#5, 20#5, 21#5, 22#5, 23#5, 30#5]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (SszArm.Serialize.Finish.returned_saved s 19#5 136 (by simp [saved])).trans
          (before.words 19#5 136 (by simp [saved]))
      · exact (SszArm.Serialize.Finish.returned_saved s 20#5 128 (by simp [saved])).trans
          (before.words 20#5 128 (by simp [saved]))
      · exact (SszArm.Serialize.Finish.returned_saved s 21#5 120 (by simp [saved])).trans
          (before.words 21#5 120 (by simp [saved]))
      · exact (SszArm.Serialize.Finish.returned_saved s 22#5 112 (by simp [saved])).trans
          (before.words 22#5 112 (by simp [saved]))
      · exact (SszArm.Serialize.Finish.returned_saved s 23#5 104 (by simp [saved])).trans
          (before.words 23#5 104 (by simp [saved]))
      · exact (SszArm.Serialize.Finish.returned_saved s 30#5 96 (by simp [saved])).trans
          (before.words 30#5 96 (by simp [saved]))
    · have notSP : reg ≠ 31#5 := by bv_omega
      have untouched : reg ∉ [19#5, 20#5, 21#5, 22#5, 23#5, 30#5, 31#5] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at member ⊢
        exact ⟨member.1, member.2.1, member.2.2.1, member.2.2.2.1,
          member.2.2.2.2.1, member.2.2.2.2.2, notSP⟩
      exact (SszArm.Serialize.Finish.returned_other s reg untouched).trans
        (before.registers reg lower upper member)
  · intro reg lower upper
    rw [SszArm.Serialize.Finish.returned_vector]
    exact before.vectors reg lower upper

end SszArm.Codec.Serialize
