import SszArm.CodecFixedBody

namespace SszArm.Codec.Fixed.IsFixed

/-- A real callee or a lowering spill touches only memory below the body SP.
The three caller save slots remain readable with their original contents. -/
theorem BodyContext.lower_frame {source current final : ArmState} {bytes : Nat}
    (context : BodyContext source current)
    (enough : 32 + bytes ≤ (r (.GPR 31#5) source).toNat)
    (sp : r (.GPR 31#5) final = r (.GPR 31#5) current)
    (frame : Delimited.MemoryFrame (Stack.envelope (r (.GPR 31#5) current).toNat bytes) current final)
    (registers : ∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 30 →
      reg ≠ 19#5 → reg ≠ 20#5 → reg ≠ 30#5 → r (.GPR reg) final = r (.GPR reg) current)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) final).setWidth 64 = (r (.SFP reg) current).setWidth 64) :
    BodyContext source final := by
  have bodyLow : 32 ≤ (r (.GPR 31#5) source).toNat := by omega
  have bodyNat : (r (.GPR 31#5) current).toNat = (r (.GPR 31#5) source).toNat - 32 := by
    rw [context.saved.sp]
    exact Stack.sub_toNat _ 32 bodyLow
  have slotRead (offset : Nat) (inside : offset + 8 ≤ 32) :
      read_mem_bytes 8 (bodySP source + BitVec.ofNat 64 offset) final =
        read_mem_bytes 8 (bodySP source + BitVec.ofNat 64 offset) current := by
    apply frame.read _ 8
    · simp only [bodySP]
      bv_omega
    · have address : (bodySP source + BitVec.ofNat 64 offset).toNat =
          (r (.GPR 31#5) source).toNat - 32 + offset := by
        simp only [bodySP]
        bv_omega
      rw [bodyNat, address]
      exact Stack.caller_slot_protected enough inside
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨sp.trans context.saved.sp, ?_, ?_, ?_⟩
    · exact (by simpa using slotRead 0 (by decide)).trans context.saved.link
    · exact (slotRead 16 (by decide)).trans context.saved.first
    · exact (slotRead 24 (by decide)).trans context.saved.second
  · intro reg lower upper h19 h20 h30
    exact (registers reg lower upper h19 h20 h30).trans
      (context.registers reg lower upper h19 h20 h30)
  · intro reg lower upper
    exact (vectors reg lower upper).trans (context.vectors reg lower upper)

theorem BodyContext.after_call {source current final : ArmState}
    {desc : SszNative.Codec.Desc} (context : BodyContext source current)
    (enough : 32 + isFixedStack desc ≤ (r (.GPR 31#5) source).toNat)
    (post : Post current final desc) : BodyContext source final := by
  apply context.lower_frame enough post.returned.sp post.frame
  · intro reg lower upper h19 h20 h30
    by_cases platform : reg = 18#5
    · subst reg
      exact post.platform
    · exact post.returned.registers reg (by bv_omega) upper
  · exact post.returned.vectors

end SszArm.Codec.Fixed.IsFixed
