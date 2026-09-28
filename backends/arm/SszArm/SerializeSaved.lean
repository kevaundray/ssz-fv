import SszArm.SerializeMeasure
import SszArm.SerializeFinishReturn

namespace SszArm.Serialize

open Delimited (Span Protected MemoryFrame)

/-- The measurement callee restores the wrapper's working registers while the
entry-saved caller registers remain in the original wrapper activation. -/
theorem Measured.savedFrom {s t : ArmState} {base : BitVec 64} {desc : SszNative.Serialize.Desc}
    {value : SszNative.Serialize.Value} (measurement : Measured s t base desc value) :
    Finish.SavedFrom s t := by
  refine ⟨?_, ?_, ?_, measurement.vectors⟩
  · change r (.GPR 31#5) t + 144#64 = r (.GPR 31#5) s
    rw [measurement.registers.stack]
    simp [Args.bodySP, Args.ofEntry, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  · intro reg displacement member
    change read_mem_bytes 8 (r (.GPR 31#5) t + BitVec.ofNat 64 displacement) t = _
    rw [measurement.registers.stack]
    exact measurement.saved reg displacement member
  · intro reg low high outside
    have notLR : reg ≠ 30#5 := by
      intro same
      subst reg
      exact outside (by simp)
    have below : reg.toNat ≤ 29 := by bv_omega
    apply measurement.untouched reg low below
    intro member
    apply outside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with h | h | h | h | h <;> simp [h]

/-- Transport saved observations across a proved local write frame. The byte
protection concerns the original save slots, not a future ABI postcondition. -/
theorem Finish.SavedFrom.of_frame {s t u : ArmState} {writes : List Span}
    (savedFrom : Finish.SavedFrom s t) (frame : MemoryFrame writes t u)
    (stack : Finish.sp u = Finish.sp t)
    (physical : (Finish.sp t).toNat + 144 ≤ 2^64)
    (saveProtected : Protected writes ((Finish.sp t).toNat + 96) 48)
    (registers : ∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 30 →
      reg ∉ [19#5, 20#5, 21#5, 22#5, 23#5, 30#5] → r (.GPR reg) u = r (.GPR reg) t)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) u).setWidth 64 = (r (.SFP reg) t).setWidth 64) :
    Finish.SavedFrom s u := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stack]
    exact savedFrom.stack
  · intro reg displacement member
    have range : 96 ≤ displacement ∧ displacement + 8 ≤ 144 := by
      simp only [Finish.saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [stack]
    have address : (Finish.sp t + BitVec.ofNat 64 displacement).toNat =
        (Finish.sp t).toNat + displacement := by bv_omega
    have fieldProtected : Protected writes
        (Finish.sp t + BitVec.ofNat 64 displacement).toNat 8 := by
      rw [address]
      have piece := saveProtected.subspan (displacement - 96) 8 (by omega)
      have offsetEq : (Finish.sp t).toNat + 96 + (displacement - 96) =
          (Finish.sp t).toNat + displacement := by omega
      simpa only [offsetEq] using piece
    rw [frame.read _ 8 (by rw [address]; omega) fieldProtected]
    exact savedFrom.words reg displacement member
  · intro reg low high outside
    exact (registers reg low high outside).trans (savedFrom.registers reg low high outside)
  · intro reg low high
    exact (vectors reg low high).trans (savedFrom.vectors reg low high)

end SszArm.Serialize
