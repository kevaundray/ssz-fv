import SszArm.NatMulWordScanDispatch

namespace SszArm.NatMulWord

open UintCodec SszNative.Limbs

/-- Every model outcome permits the same actual helper stack envelope. -/
theorem stack_member (s : ArmState) (operand : SszNative.NatOperand) (factor : BitVec 64) :
    ((r (.GPR 31#5) s).toNat - 48, 48) ∈ writesFor s (outcome s operand factor) := by
  cases allocation : (outcome s operand factor).allocation <;>
    cases result : (outcome s operand factor).result <;>
    simp [writesFor, localWrites, allocation, result]

theorem Owned.scan_source {s : ArmState} {pointer factor : BitVec 64}
    {words : List (BitVec 64)} (owned : Owned s (.large pointer words) factor) :
    NatCompare.Source s pointer words := by
  refine ⟨by have := owned.stackBound; omega, owned.operandAt.2.2.1, ?_⟩
  by_cases empty : words = []
  · exact Or.inl empty
  · right
    have protectedInput := owned.inputOwned
    change Delimited.Protected (writesFor s (outcome s (.large pointer words) factor))
      pointer.toNat (8 * words.length) at protectedInput
    rcases protectedInput with zero | separate
    · have positive := List.length_pos_iff.mpr empty
      omega
    · have apart := separate _ (stack_member s (.large pointer words) factor)
      have stack := owned.stackBound
      simp only [Prod.fst, Prod.snd] at apart
      omega

theorem Owned.scan_words {s : ArmState} {pointer factor : BitVec 64}
    {words : List (BitVec 64)} (owned : Owned s (.large pointer words) factor) :
    NatCompare.Words s pointer words := by
  intro i
  apply BitVec.eq_of_toNat_eq
  have hi := Option.some.inj (owned.operandAt.2.2.2 i)
  simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using hi

theorem normalized_small (word : BitVec 64) :
    (SszNative.NatOperand.small word).normalized = .small word := by
  by_cases zero : word = 0#64 <;>
    simp [SszNative.NatOperand.normalized, SszNative.NatOperand.fromWords,
      SszNative.NatOperand.pointer, SszNative.NatOperand.words, trim, zero]

/-- Original entry to the exact identity return entrance for every raw input.
All current-memory premises of the indexed reads are derived from Owned. -/
theorem identity_ready (s : ArmState) (base : BitVec 64) (operand : SszNative.NatOperand)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (owned : Owned s operand 1#64) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ IdentityReady base operand t := by
  obtain ⟨fuel, u, hu, huf, huk, hup⟩ :=
    word_dispatch s base 1#64 hc he ha hp owned.factorRegister
  have hu100 : read_pc u = base + 100#64 := by simpa using hup
  cases operand with
  | small word =>
    have hu1 : r (.GPR 1#5) u = 0#64 := (huk _).trans owned.pointer
    have hu2 : r (.GPR 2#5) u = word := (huk _).trans owned.payload
    let t := block base [.p100] u
    have hpc : r .PC u = base + 100#64 := hu100
    have hf : Follows base [.p100] u := by simp [Follows, Op.row, hpc]
    have ht : run 1 u = t := block_run base [.p100] u
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) hf
    refine ⟨fuel + 1, t, ?_, huf.trans (scan_pure_frame base [.p100] u (by decide)), Or.inr ?_⟩
    · rw [run_plus, hu, ht]
    · simp [t, block, Op.effect, put, next, state_simp_rules, hu1, hu2,
        normalized_small, SszNative.NatOperand.pointer, SszNative.NatOperand.payload]
  | large pointer words =>
    have hn : pointer ≠ 0#64 := by
      intro zero
      have positive := owned.operandAt.1
      simp [zero] at positive
    obtain ⟨extra, t, ht, htf, ready⟩ := identity_large u base pointer words
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) hu100 hn
      ((huk _).trans owned.pointer) ((huk _).trans owned.payload)
      (huf.source _ _ owned.scan_source) (huf.words _ _ owned.scan_source owned.scan_words)
    refine ⟨fuel + extra, t, ?_, huf.trans htf, ready⟩
    rw [run_plus, hu, ht]

/-- Entry-through-scan dispatch for every raw Large operand and every general
factor. The small arithmetic path observes the original low limb. -/
theorem general_large_ready (s : ArmState) (base pointer factor : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (owned : Owned s (.large pointer words) factor)
    (factorZero : factor ≠ 0#64) (factorOne : factor ≠ 1#64) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ r (.GPR 1#5) t = pointer ∧
      r (.GPR 8#5) t = trimBias words - BitVec.ofNat 64 (8 * (sigWords words - 1)) ∧
      (if sigWords words ≤ 1 then
        read_pc t = base + 928#64 ∧ r (.GPR 2#5) t = words[0]?.getD 0#64
       else read_pc t = base + 320#64 ∧ r (.GPR 2#5) t = BitVec.ofNat 64 words.length ∧
        r (.GPR 9#5) t = BitVec.ofNat 64 (sigWords words) ∧
        r (.GPR 12#5) t = BitVec.ofNat 64 (sigWords words - 1)) := by
  obtain ⟨fuel, u, hu, huf, huk, hup⟩ :=
    word_dispatch s base factor hc he ha hp owned.factorRegister
  have hu228 : read_pc u = base + 228#64 := by simpa [factorZero, factorOne] using hup
  have hn : pointer ≠ 0#64 := by
    intro zero
    have positive := owned.operandAt.1
    simp [zero] at positive
  obtain ⟨extra, v, hv, hvf, hv1, hv2, hv8, hvp, hv9⟩ := trim_scan_entry u base pointer words
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hu228 hn
    ((huk _).trans owned.pointer) ((huk _).trans owned.payload)
    (huf.source _ _ owned.scan_source) (huf.words _ _ owned.scan_source owned.scan_words)
  have hsf := huf.trans hvf
  obtain ⟨last, t, ht, htf, ht1, ht8, ready⟩ := trim_normalize_exit v base pointer words
    (hsf.code hc) (hsf.error.trans he) (hsf.aligned ha) hvp hv1 hv2 hv9
    (hsf.source _ _ owned.scan_source) (hsf.words _ _ owned.scan_source owned.scan_words)
  refine ⟨fuel + extra + last, t, ?_, hsf.trans htf, ht1, ht8.trans hv8, ready⟩
  rw [run_plus, run_plus, hu, hv, ht]

end SszArm.NatMulWord
