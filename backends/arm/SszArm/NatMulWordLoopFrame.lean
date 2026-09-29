import SszArm.NatMulWordRoundValues
import SszArm.NatMulLoopMemoryFrame

namespace SszArm.NatMulWord

open Delimited (MemoryFrame)

/-- The loop modifies only its index, carry, next index and product pair. -/
structure LoopStable (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [13#5, 14#5, 16#5, 17#5, 18#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem LoopStable.refl (s : ArmState) : LoopStable s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem LoopStable.sp {s t : ArmState} (stable : LoopStable s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := stable.registers _ (by decide)

theorem LoopStable.trans {s t u : ArmState} (st : LoopStable s t) (tu : LoopStable t u) :
    LoopStable s u :=
  ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg keep => (tu.registers reg keep).trans (st.registers reg keep),
    fun reg => (tu.vectors reg).trans (st.vectors reg)⟩

theorem LoopStable.code {s t : ArmState} (stable : LoopStable s t)
    {base : BitVec 64} (code : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, stable.program] using code

theorem LoopStable.aligned {s t : ArmState} (stable : LoopStable s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, stable.sp] using aligned

theorem loop_block_vectors (base : BitVec 64) (ops : List Op) (s : ArmState)
    (reg : BitVec 5) : r (.SFP reg) (block base ops s) = r (.SFP reg) s := by
  apply NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (fun t => r (.SFP reg) t) ops s
  intro op _ t
  exact op.sfp base t reg

theorem round_completed_stable (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (roundAddress s).toNat + 8 ≤ 2^64)
    (separate : (roundAddress s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 48 ∨
      (r (.GPR 31#5) s).toNat ≤ (roundAddress s).toNat) :
    LoopStable s (roundCompleted s base) := by
  constructor
  · simp only [roundCompleted, roundTail, roundStored, roundAdded, roundHigh,
      roundLow, block_program, high_completed_program, Op.program]
  · simp only [roundCompleted, roundTail, roundStored, roundAdded, roundHigh,
      roundLow, block_error, high_completed_error, Op.error]
  · intro reg keep
    exact round_completed_registers s base stack physical separate reg
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
  · intro reg
    simp only [roundCompleted, roundTail, roundStored, roundAdded, roundHigh,
      highCompleted, roundLow, loop_block_vectors, Op.sfp]

theorem round_completed_index (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (roundAddress s).toNat + 8 ≤ 2^64)
    (separate : (roundAddress s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 48 ∨
      (r (.GPR 31#5) s).toNat ≤ (roundAddress s).toNat) :
    r (.GPR 13#5) (roundCompleted s base) = r (.GPR 16#5) s := by
  rw [roundCompleted, round_tail_index,
    round_stored_field s base stack physical separate (.GPR 16#5) (by decide)]
  exact round_added_registers s base stack 16#5 (by decide) (by decide)

theorem round_completed_pc (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (roundAddress s).toNat + 8 ≤ 2^64)
    (separate : (roundAddress s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 48 ∨
      (r (.GPR 31#5) s).toNat ≤ (roundAddress s).toNat) :
    read_pc (roundCompleted s base) =
      if r (.GPR 9#5) s = r (.GPR 16#5) s then base + 1464#64 else base + 812#64 := by
  rw [roundCompleted, round_tail_pc,
    round_stored_field s base stack physical separate (.GPR 9#5) (by decide),
    round_stored_field s base stack physical separate (.GPR 16#5) (by decide),
    round_added_registers s base stack 9#5 (by decide) (by decide),
    round_added_registers s base stack 16#5 (by decide) (by decide)]

/-- Exact spill and single output-cell frame, plus the word actually stored. -/
theorem round_completed_memory (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (roundAddress s).toNat + 8 ≤ 2^64)
    (separate : (roundAddress s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 48 ∨
      (r (.GPR 31#5) s).toNat ≤ (roundAddress s).toNat) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48), ((roundAddress s).toNat, 8)]
      s (roundCompleted s base) ∧
    read_mem_bytes 8 (roundAddress s) (roundCompleted s base) =
      r (.GPR 18#5) (roundCompleted s base) := by
  have address : storeAddress (roundAdded s base) = roundAddress s := by
    unfold storeAddress roundAddress
    rw [round_added_registers s base stack 15#5 (by decide) (by decide),
      round_added_registers s base stack 13#5 (by decide) (by decide)]
  have sp := round_added_registers s base stack 31#5 (by decide) (by decide)
  have highFrame := high_completed_frame .loop (roundLow s base) base
    (by simpa [roundLow, Op.effect, put, next, state_simp_rules] using stack)
  have before : MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48)] s (roundAdded s base) := by
    intro a outside
    simpa [roundAdded, roundHigh, roundLow, Op.effect, put, next, state_simp_rules] using
      highFrame a (by simpa [roundLow, Op.effect, put, next, state_simp_rules] using outside)
  have after := store_frame (roundAdded s base) (by rw [sp]; omega)
    (by rw [address]; exact physical)
  have mem : (roundCompleted s base).mem = (storeMemory (roundAdded s base)).mem := by
    rw [roundCompleted, round_tail_memory, round_store_effect s base stack physical separate]
    simp only [ArmState.mem_w_eq_mem]
  constructor
  · intro a outside
    rw [mem]
    refine (after a ?_).trans (before a ?_)
    · intro span member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · have h := outside ((r (.GPR 31#5) s).toNat - 48, 48) (by simp)
        simp only [Prod.fst, Prod.snd] at h ⊢
        rw [sp]
        omega
      · simpa only [address] using outside ((roundAddress s).toNat, 8) (by simp)
    · intro span member
      simp only [List.mem_singleton] at member
      exact outside span (by simp only [List.mem_cons, member, true_or])
  · have observed := stored_word (roundAdded s base) (by rw [address]; exact physical)
    rw [address] at observed
    have value : r (.GPR 18#5) (roundCompleted s base) =
        r (.GPR 18#5) (roundAdded s base) := by
      rw [roundCompleted, round_tail_registers _ _ 18#5 (by decide) (by decide),
        round_stored_field s base stack physical separate (.GPR 18#5) (by decide)]
    exact (Memory.mem_eq_iff_read_mem_bytes_eq.mp mem 8 (roundAddress s)).trans
      (observed.trans value.symm)

end SszArm.NatMulWord
