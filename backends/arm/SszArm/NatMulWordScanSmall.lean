import SszArm.NatMulWordIdentityOwned

namespace SszArm.NatMulWord

/-- A raw Small operand bypasses the high-zero scan and reaches the original
48-byte single-word multiplication entry with its exact payload unchanged. -/
theorem general_small_ready (s : ArmState) (base word factor : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (owned : Owned s (.small word) factor)
    (factorZero : factor ≠ 0#64) (factorOne : factor ≠ 1#64) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ read_pc t = base + 928#64 ∧
      r (.GPR 1#5) t = 0#64 ∧ r (.GPR 2#5) t = word ∧
      (∀ reg : BitVec 5, r (.GPR reg) t = r (.GPR reg) s) := by
  obtain ⟨fuel, u, hu, huf, huk, hup⟩ :=
    word_dispatch s base factor hc he ha hp owned.factorRegister
  have hu228 : read_pc u = base + 228#64 := by simpa [factorZero, factorOne] using hup
  have hu1 : r (.GPR 1#5) u = 0#64 := (huk _).trans owned.pointer
  have hu2 : r (.GPR 2#5) u = word := (huk _).trans owned.payload
  let t := block base [.p228] u
  have hpc : r .PC u = base + 228#64 := hu228
  have hf : Follows base [.p228] u := by simp [Follows, Op.row, hpc]
  have ht : run 1 u = t := block_run base [.p228] u
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hf
  refine ⟨fuel + 1, t, ?_, huf.trans (scan_pure_frame base [.p228] u (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [run_plus, hu, ht]
  · simp [t, block, Op.effect, put, next, state_simp_rules, hu1]
  · simp [t, block, Op.effect, put, next, state_simp_rules, hu1]
  · simp [t, block, Op.effect, put, next, state_simp_rules, hu2]
  · intro reg
    simpa [t, block, Op.effect, put, next, state_simp_rules] using huk reg

end SszArm.NatMulWord
