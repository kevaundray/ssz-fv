import SszArm.HashMemory

namespace SszArm.Hash

open Delimited (Span Protected MemoryFrame)

theorem protected_writes_mono {small large : List Span} {address bytes : Nat}
    (owned : Protected large address bytes)
    (contained : ∀ span ∈ small, ∃ outer ∈ large,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2) :
    Protected small address bytes := by
  rcases owned with empty | separate
  · exact Or.inl empty
  · right
    intro span member
    obtain ⟨outer, inLarge, lo, hi⟩ := contained span member
    have apart := separate outer inLarge
    omega

/-- The 112-byte consumed copy occupies the upper local frame, while the
192-byte finalizer activation is strictly below the combine body's SP. -/
theorem combine_finalize_writes (s q : ArmState) (base : BitVec 64) (left right : ByteArray)
    (owned : CombineOwned s base left right)
    (sp : r (.GPR 31#5) q = r (.GPR 31#5) s - 304#64)
    (out : r (.GPR 0#5) q = r (.GPR 0#5) s)
    (state : r (.GPR 1#5) q = r (.GPR 31#5) q + 112#64) :
    ∀ span ∈ finalizeWrites q, ∃ outer ∈ combineWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
  have low := owned.stackLow
  have spNat : (r (.GPR 31#5) q).toNat = (r (.GPR 31#5) s).toNat - 304 := by
    rw [sp]; bv_omega
  have stateNat : (r (.GPR 1#5) q).toNat = (r (.GPR 31#5) s).toNat - 192 := by
    rw [state, sp]; bv_omega
  intro span member
  simp only [finalizeWrites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · refine ⟨stackSpan s 496, by simp [combineWrites], ?_, ?_⟩ <;>
      simp only [stackSpan, spNat] <;> omega
  · refine ⟨((r (.GPR 0#5) s).toNat, 32), by simp [combineWrites], ?_, ?_⟩ <;>
      simp only [out, Nat.le_refl]
  · refine ⟨stackSpan s 496, by simp [combineWrites], ?_, ?_⟩ <;>
      simp only [stackSpan, stateNat] <;> omega

theorem combine_finalize_owned (s q : ArmState) (base : BitVec 64) (left right : ByteArray)
    (value : StreamState) (owned : CombineOwned s base left right)
    (sp : r (.GPR 31#5) q = r (.GPR 31#5) s - 304#64)
    (out : r (.GPR 0#5) q = r (.GPR 0#5) s)
    (state : r (.GPR 1#5) q = r (.GPR 31#5) q + 112#64)
    (represented : StateAt q (r (.GPR 1#5) q) value) : FinalizeOwned q base value := by
  have low := owned.stackLow
  have spNat : (r (.GPR 31#5) q).toNat = (r (.GPR 31#5) s).toNat - 304 := by
    rw [sp]; bv_omega
  have stateNat : (r (.GPR 1#5) q).toNat = (r (.GPR 31#5) s).toNat - 192 := by
    rw [state, sp]; bv_omega
  have outputApart : (r (.GPR 0#5) s).toNat + 32 ≤ (r (.GPR 31#5) s).toNat - 496 ∨
      (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat := by
    rcases owned.outputStack with empty | separate
    · omega
    · have apart := separate (stackSpan s 496) (by simp)
      simp only [stackSpan] at apart
      omega
  have inclusion := combine_finalize_writes s q base left right owned sp out state
  constructor
  · exact represented
  · rw [stateNat]
    have upper := (r (.GPR 31#5) s).isLt
    omega
  · simpa only [out] using owned.outputBound
  · rw [spNat]; omega
  · right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    simp only [stackSpan, spNat, stateNat]
    omega
  · right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    simp only [stackSpan, spNat, out]
    omega
  · right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    simp only [stateNat, out]
    omega
  · exact protected_writes_mono owned.initialOwned inclusion
  · exact protected_writes_mono owned.roundsOwned inclusion

/-- Finalization cannot overwrite the original combine callee-save slots. -/
theorem combine_finalize_saved (s q : ArmState) (base : BitVec 64) (left right : ByteArray)
    (owned : CombineOwned s base left right)
    (sp : r (.GPR 31#5) q = r (.GPR 31#5) s - 304#64)
    (out : r (.GPR 0#5) q = r (.GPR 0#5) s)
    (state : r (.GPR 1#5) q = r (.GPR 31#5) q + 112#64) :
    Protected (finalizeWrites q) (r (.GPR 31#5) q + 224#64).toNat 80 := by
  have low := owned.stackLow
  have spNat : (r (.GPR 31#5) q).toNat = (r (.GPR 31#5) s).toNat - 304 := by
    rw [sp]; bv_omega
  have stateNat : (r (.GPR 1#5) q).toNat = (r (.GPR 31#5) s).toNat - 192 := by
    rw [state, sp]; bv_omega
  have savedNat : (r (.GPR 31#5) q + 224#64).toNat = (r (.GPR 31#5) s).toNat - 80 := by
    rw [sp]; bv_omega
  have outputApart : (r (.GPR 0#5) s).toNat + 32 ≤ (r (.GPR 31#5) s).toNat - 496 ∨
      (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat := by
    rcases owned.outputStack with empty | separate
    · omega
    · have apart := separate (stackSpan s 496) (by simp)
      simp only [stackSpan] at apart
      omega
  right
  intro span member
  simp only [finalizeWrites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · simp only [stackSpan, spNat, savedNat]; omega
  · simp only [out, savedNat]; omega
  · simp only [stateNat, savedNat]; omega

end SszArm.Hash
