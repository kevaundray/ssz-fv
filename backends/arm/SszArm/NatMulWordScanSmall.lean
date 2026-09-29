import SszArm.NatMulWordIdentityOwned

namespace SszArm.NatMulWord

private theorem small_branch_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (block base [.p228] s) = r (.GPR reg) s := by
  change r (.GPR reg) (Op.p228.effect base s) = _
  simp only [Op.effect, NatCompare.r_gpr_of_w_pc]

private theorem small_branch_pc (s : ArmState) (base : BitVec 64)
    (zero : r (.GPR 1#5) s = 0#64) :
    read_pc (block base [.p228] s) = base + 928#64 := by
  change r .PC (Op.p228.effect base s) = _
  simp only [Op.effect, r_of_w_same, zero, ↓reduceIte]

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
  have hf : Follows base [.p228] u := ⟨hu228, trivial⟩
  have ht : run 1 u = t := block_run base [.p228] u
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hf
  refine ⟨fuel + 1, t, ?_, huf.trans (scan_pure_frame base [.p228] u (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [run_plus, hu, ht]
  · exact small_branch_pc u base hu1
  · exact (small_branch_register u base 1#5).trans hu1
  · exact (small_branch_register u base 2#5).trans hu2
  · intro reg
    exact (small_branch_register u base reg).trans (huk reg)

end SszArm.NatMulWord
