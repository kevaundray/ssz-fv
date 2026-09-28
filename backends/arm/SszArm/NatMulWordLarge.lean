import SszArm.NatMulWordLargeAllocated

namespace SszArm.NatMulWord.Large

open SszNative.NatArithmetic

/-- Actual PC320 through an original error RET or the complete allocating
loop/normalization RET. Ownership and register premises concern this state only. -/
theorem checkpoint_run (s : ArmState) (base : BitVec 64) (operand : SszNative.NatOperand)
    (factor : BitVec 64) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (owned : Owned s operand factor)
    (pc : read_pc s = base + 320#64) (nonzero : factor ≠ 0#64) (notone : factor ≠ 1#64)
    (large : 1 < operand.wordCount)
    (countReg : r (.GPR 9#5) s = BitVec.ofNat 64 operand.wordCount)
    (lastReg : r (.GPR 12#5) s = BitVec.ofNat 64 (operand.wordCount - 1))
    (bias : r (.GPR 8#5) s = -BitVec.ofNat 64 (8 * operand.wordCount)) :
    ∃ fuel t, run fuel s = t ∧ Post s t operand factor := by
  cases operand with
  | small word =>
    have count := SszNative.Limbs.sigWords_le_length [word]
    simp only [List.length_singleton] at count
    simp only [SszNative.NatOperand.wordCount, SszNative.NatOperand.words] at large
    omega
  | large raw rawWords =>
    let operand : SszNative.NatOperand := .large raw rawWords
    let address := read_mem_bytes 8 (r (.GPR 4#5) s) s
    let capacity := read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s
    let used := read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s
    have physicalCount := Reserve.physical_count_add_one s operand owned.operandAt
    have countNat : (r (.GPR 9#5) s).toNat = operand.wordCount := by
      rw [countReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have headerStack : (r (.GPR 4#5) s).toNat + 24 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
        (r (.GPR 31#5) s).toNat ≤ (r (.GPR 4#5) s).toNat := by
      rcases owned.arenaLocal with empty | separate
      · omega
      · have apart := separate ((r (.GPR 31#5) s).toNat - 48, 48)
          (small_stack_local s (outcome s operand factor))
        have stack := owned.stackBound
        simp only [Prod.fst, Prod.snd] at apart
        omega
    obtain ⟨fuel, u, ran, prior, selected⟩ := Reserve.large_checks_runs s base address capacity used
      code error aligned pc (by have := owned.stackBound; omega) owned.arenaBound headerStack rfl rfl rfl
    rw [countNat] at selected
    rcases selected with ⟨overflow, _⟩ | ⟨countFits, selected⟩
    · omega
    · rcases selected with ⟨failed, exit⟩ | ⟨checks, exit, baseReg, startReg, finishReg, keep12, pointerReg⟩
      · have model : outcome s operand factor = unchanged (arenaOf s).used (.error .scratchExhausted) := by
          unfold outcome
          rw [SszNative.NatMul.runWord_large operand factor _ _ _ nonzero notone large,
            if_pos physicalCount, failed]
        obtain ⟨lastRun, post⟩ := error_finish s u base operand factor .scratch owned
          (reserve_small prior owned.stackBound) code error aligned exit model
        exact ⟨fuel + 50, errorResult .scratch base u, by rw [run_plus, ran, lastRun], post⟩
      · exact allocated_run s u base raw factor rawWords code error aligned owned nonzero notone large
          countReg lastReg bias prior exit checks (congrArg BitVec.toNat baseReg) startReg finishReg keep12 pointerReg

end SszArm.NatMulWord.Large

namespace SszArm.NatMulWord

/-- Original entry-through-original-RET refinement for the multiword general
factor branch, including every real scratch-exhaustion guard. -/
theorem large_run (s : ArmState) (base : BitVec 64) (operand : SszNative.NatOperand)
    (factor : BitVec 64) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (owned : Owned s operand factor)
    (pc : read_pc s = base + BitVec.ofNat 64 entry)
    (nonzero : factor ≠ 0#64) (notone : factor ≠ 1#64) (large : 1 < operand.wordCount) :
    ∃ fuel t, run fuel s = t ∧ Post s t operand factor := by
  have entryPC : read_pc s = base := by simpa only [entry, BitVec.ofNat_zero, BitVec.add_zero] using pc
  obtain ⟨fuel, u, ran, scan, pointer, ready⟩ :=
    general_ready s base factor operand code error aligned entryPC owned nonzero notone
  have priorFrame := scan.small owned.stackBound
  simp only [GeneralReady, if_neg (by omega : ¬ operand.wordCount ≤ 1)] at ready
  obtain ⟨at320, payload, countReg, lastReg, bias⟩ := ready
  have currentOwned := Large.scan_owned owned priorFrame pointer payload
  obtain ⟨rest, t, restRun, post⟩ := Large.checkpoint_run u base operand factor
    (priorFrame.code code) (priorFrame.error.trans error) (priorFrame.aligned aligned)
    currentOwned at320 nonzero notone large countReg lastReg
    (bias.trans (Large.trim_bias_count operand.words operand.wordCount (by omega)))
  exact ⟨fuel + rest, t, by rw [run_plus, ran, restRun], Large.scan_post owned priorFrame post⟩

end SszArm.NatMulWord
