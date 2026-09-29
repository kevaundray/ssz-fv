import SszArm.CodecFixedMeasureEpilogue

namespace SszArm.Codec.Fixed.MeasureFixed

open Delimited (MemoryFrame Protected Returned)

/-- Every saved word lies in the original, physically addressable activation. -/
theorem saved_slot_bound (source : ArmState)
    (low : 160 ≤ (r (.GPR 31#5) source).toNat)
    (reg : BitVec 5) (offset : Nat) (member : (reg, offset) ∈ savedRegisters) :
    ((Args.ofEntry source).bodySP + BitVec.ofNat 64 offset).toNat + 8 ≤ 2^64 := by
  have within : offset + 8 ≤ 160 := by
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  simp only [Args.bodySP, Args.ofEntry]
  bv_omega

theorem Saved.preserved {source current final : ArmState} {writes : List Delimited.Span}
    (saved : Saved source current) (low : 160 ≤ (r (.GPR 31#5) source).toNat)
    (frame : MemoryFrame writes current final)
    (sp : r (.GPR 31#5) final = r (.GPR 31#5) current)
    (slots : ∀ reg offset, (reg, offset) ∈ savedRegisters →
      Protected writes ((Args.ofEntry source).bodySP + BitVec.ofNat 64 offset).toNat 8) :
    Saved source final := by
  refine ⟨sp.trans saved.sp, ?_⟩
  intro reg offset member
  exact (frame.read _ 8 (saved_slot_bound source low reg offset member)
    (slots reg offset member)).trans (saved.slots reg offset member)

theorem Context.preserved {source current final : ArmState} {writes : List Delimited.Span}
    (context : Context source current) (low : 160 ≤ (r (.GPR 31#5) source).toNat)
    (frame : MemoryFrame writes current final)
    (sp : r (.GPR 31#5) final = r (.GPR 31#5) current)
    (registers : ∀ reg : BitVec 5, 27 ≤ reg.toNat → reg.toNat ≤ 29 →
      r (.GPR reg) final = r (.GPR reg) current)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) final).setWidth 64 = (r (.SFP reg) current).setWidth 64)
    (slots : ∀ reg offset, (reg, offset) ∈ savedRegisters →
      Protected writes ((Args.ofEntry source).bodySP + BitVec.ofNat 64 offset).toNat 8) :
    Context source final := by
  refine ⟨context.saved.preserved low frame sp slots, ?_, ?_⟩
  · intro reg lower upper
    exact (registers reg lower upper).trans (context.registers reg lower upper)
  · intro reg lower upper
    exact (vectors reg lower upper).trans (context.vectors reg lower upper)

/-- Actual helper return and its physical frame transport the caller activation. -/
theorem Context.after_call {source current final : ArmState} {writes : List Delimited.Span}
    (context : Context source current) (low : 160 ≤ (r (.GPR 31#5) source).toNat)
    (frame : MemoryFrame writes current final) (returned : Returned current final)
    (slots : ∀ reg offset, (reg, offset) ∈ savedRegisters →
      Protected writes ((Args.ofEntry source).bodySP + BitVec.ofNat 64 offset).toNat 8) :
    Context source final := by
  apply context.preserved low frame returned.sp
  · intro reg lower upper
    exact returned.registers reg (by omega) (by omega)
  · exact returned.vectors
  · exact slots

end SszArm.Codec.Fixed.MeasureFixed
