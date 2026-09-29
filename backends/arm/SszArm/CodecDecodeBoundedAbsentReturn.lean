import SszArm.CodecDecodeBoundedAbsent

namespace SszArm.Codec.Decode.Bounded

open Delimited (Returned)

/-- Every saved register is read from its actual prologue slot after the
lowered status store; the unwritten eight-byte stack gap stays outside ownership. -/
theorem absent_saved (s : ArmState) (base : BitVec 64) (actual : SszNative.NatOperand)
    (owned : Owned s none actual) (reg : BitVec 5) (offset : Nat)
    (member : (reg, offset) ∈ savedRegisters) :
    read_mem_bytes 8 (bodySP s + BitVec.ofNat 64 offset)
      (Emit.statusStored (tagRead (prologue s base) base)) = r (.GPR reg) s := by
  have low := owned.stackBound
  have bound := owned.resultBound
  rcases owned.outputStack with empty | separate
  · omega
  have link := separate ((r (.GPR 31#5) s).toNat - 48, 8) (by simp [stackWrites])
  have saved := separate ((r (.GPR 31#5) s).toNat - 32, 32) (by simp [stackWrites])
  simp only [Prod.fst, Prod.snd] at link saved
  have original := prologue_saved s base low reg offset member
  rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp (Emit.statusStored_memory _)]
  simp only [Emit.statusMemory, tagRead, state_simp_rules]
  simp only [prologue_sp, prologue_register s base _ (by decide)]
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp (disch := (simp only [bodySP]; bv_omega)) only
      [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]
    exact original

theorem absent_returned (s : ArmState) (base : BitVec 64) (actual : SszNative.NatOperand)
    (owned : Owned s none actual) (error : read_err s = .None) :
    Returned s (absentState s base) := by
  have r30 := absent_saved s base actual owned 30#5 0 (by simp [savedRegisters])
  have r22 := absent_saved s base actual owned 22#5 16 (by simp [savedRegisters])
  have r21 := absent_saved s base actual owned 21#5 24 (by simp [savedRegisters])
  have r20 := absent_saved s base actual owned 20#5 32 (by simp [savedRegisters])
  have r19 := absent_saved s base actual owned 19#5 40 (by simp [savedRegisters])
  simp only [BitVec.ofNat_zero, BitVec.add_zero] at r30
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [absentState, tagRead, state_simp_rules] using r30
  · simpa [absentState, tagRead, state_simp_rules] using error
  · simp [absentState, tagRead, state_simp_rules, bodySP, BitVec.sub_add_cancel]
  · intro reg low high
    by_cases h19 : reg = 19#5
    · subst reg; simpa [absentState, restored, tagRead, state_simp_rules] using r19
    by_cases h20 : reg = 20#5
    · subst reg; simpa [absentState, restored, tagRead, state_simp_rules] using r20
    by_cases h21 : reg = 21#5
    · subst reg; simpa [absentState, restored, tagRead, state_simp_rules] using r21
    by_cases h22 : reg = 22#5
    · subst reg; simpa [absentState, restored, tagRead, state_simp_rules] using r22
    by_cases h30 : reg = 30#5
    · subst reg; simpa [absentState, restored, tagRead, state_simp_rules] using r30
    have h8 : reg ≠ 8#5 := by bv_omega
    have h9 : reg ≠ 9#5 := by bv_omega
    have h10 : reg ≠ 10#5 := by bv_omega
    have h31 : reg ≠ 31#5 := by bv_omega
    simp [absentState, restored, tagRead, state_simp_rules,
      h19, h20, h21, h22, h30, h8, h9, h10, h31]
  · intro reg low high
    simp [absentState, tagRead, state_simp_rules]

end SszArm.Codec.Decode.Bounded
