import SszArm.NatMulWordLargeActive

namespace SszArm.NatMulWord.Large

open Delimited (Protected MemoryFrame)
open SszNative.NatArithmetic

/-- Success is selected by the already executed actual guards. Every memory
observation supplied to the loop is derived below from stores/current input. -/
theorem allocated_run (s u : ArmState) (base raw factor : BitVec 64)
    (rawWords : List (BitVec 64))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : Owned s (.large raw rawWords) factor)
    (nonzero : factor ≠ 0#64) (notone : factor ≠ 1#64)
    (large : 1 < (SszNative.NatOperand.large raw rawWords).wordCount)
    (countReg : r (.GPR 9#5) s = BitVec.ofNat 64 (SszNative.NatOperand.large raw rawWords).wordCount)
    (lastReg : r (.GPR 12#5) s = BitVec.ofNat 64 ((SszNative.NatOperand.large raw rawWords).wordCount - 1))
    (bias : r (.GPR 8#5) s = -BitVec.ofNat 64 (8 * (SszNative.NatOperand.large raw rawWords).wordCount))
    (prior : Reserve.Prefix s u) (pc : read_pc u = base + 452#64)
    (checks : SszNative.Arena.Checks (arenaOf s).base (arenaOf s).capacity (arenaOf s).used
      ((SszNative.NatOperand.large raw rawWords).wordCount + 1))
    (baseReg : (r (.GPR 10#5) u).toNat = (arenaOf s).base)
    (startReg : (r (.GPR 16#5) u).toNat = SszNative.Arena.start (arenaOf s).base (arenaOf s).used)
    (finishReg : (r (.GPR 17#5) u).toNat = SszNative.Arena.finish (arenaOf s).base (arenaOf s).used
      ((SszNative.NatOperand.large raw rawWords).wordCount + 1))
    (keep12 : r (.GPR 12#5) u = r (.GPR 12#5) s)
    (pointerReg : (r (.GPR 15#5) u).toNat =
      (arenaOf s).base + SszNative.Arena.start (arenaOf s).base (arenaOf s).used) :
    ∃ fuel t, run fuel s = t ∧ Post s t (.large raw rawWords) factor := by
  let operand : SszNative.NatOperand := .large raw rawWords
  let count := operand.wordCount
  have countLarge : 1 < count := large
  have operandPointer : operand.pointer = raw := rfl
  have operandWords : operand.words = rawWords := rfl
  let reservation : SszNative.Arena.Reservation :=
    ⟨(arenaOf s).base + SszNative.Arena.start (arenaOf s).base (arenaOf s).used,
      SszNative.Arena.finish (arenaOf s).base (arenaOf s).used (count + 1)⟩
  let pointer := BitVec.ofNat 64 reservation.pointer
  have countBound := Reserve.physical_count_add_one s operand owned.operandAt
  have reserved : SszNative.Arena.reserve (arenaOf s).base (arenaOf s).capacity (arenaOf s).used
      (count + 1) = some reservation :=
    (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) reservation).2 ⟨checks, rfl⟩
  have model : outcome s operand factor = committed reservation (SszNative.NatMul.wordWritten operand factor) := by
    unfold outcome
    rw [SszNative.NatMul.runWord_large operand factor _ _ _ nonzero notone large,
      if_pos countBound, reserved]
  have space := allocation_space s operand factor owned reservation (by omega) reserved model
  have priorFrame : SmallFrame s u := reserve_small prior owned.stackBound
  have currentOwned : Owned u operand factor := scan_owned owned priorFrame
    ((prior.frame.registers 1#5 (by decide)).trans owned.pointer)
    ((prior.frame.registers 2#5 (by decide)).trans owned.payload)
  have positiveRaw : 0 < rawWords.length := by
    have h := SszNative.Limbs.sigWords_le_length rawWords
    change count ≤ rawWords.length at h
    omega
  have firstWord : read_mem_bytes 8 (r (.GPR 1#5) u) u = rawWords[0]?.getD 0#64 := by
    rw [currentOwned.pointer, operandPointer]
    simpa using (scan_limb u raw rawWords 0 positiveRaw currentOwned.scan_source currentOwned.scan_words).2.2
  let c := block base Reserve.firstOps u
  have setupRun : run 7 u = c := Reserve.first_run u base (priorFrame.code code)
    (priorFrame.error.trans error) (priorFrame.aligned aligned) pc
  have setup := Reserve.first_effect u base pc
  have setupABI : SmallABI s c := priorFrame.toSmallABI.trans (setup_abi u base)
  have output : r (.GPR 10#5) c = pointer := by
    apply BitVec.eq_of_toNat_eq
    rw [setup.2.2.2.2.1, BitVec.toNat_add, baseReg, startReg]
    exact (Nat.mod_eq_of_lt space.pointerBound).trans (Nat.mod_eq_of_lt space.pointerBound).symm
  have nextPointer : r (.GPR 15#5) u = pointer := by
    apply BitVec.eq_of_toNat_eq
    exact pointerReg.trans (Nat.mod_eq_of_lt space.pointerBound).symm
  have firstLow : r (.GPR 11#5) c = rawWords[0]?.getD 0#64 * factor := by
    rw [setup.2.2.2.2.2.2.2.1, firstWord, currentOwned.factorRegister]
  have firstInput : r (.GPR 14#5) c = rawWords[0]?.getD 0#64 :=
    setup.2.2.1.trans firstWord
  have width : r (.GPR 12#5) c = BitVec.ofNat 64 (count + 2) := by
    rw [setup.2.2.2.2.2.1, keep12, lastReg]
    change BitVec.ofNat 64 (count - 1) + 3#64 = BitVec.ofNat 64 (count + 2)
    have positive : 0 < count := by omega
    bv_omega
  have setupFrame : MemoryFrame (writesFor s (outcome s operand factor)) u c :=
    setup_frame_full s u base operand factor owned reservation model priorFrame.toSmallABI pc
  have currentFrame : MemoryFrame (writesFor s (outcome s operand factor)) s c :=
    (priorFrame.full (outcome s operand factor)).trans setupFrame
  have physicalOutput : (r (.GPR 10#5) c).toNat + 8 ≤ 2^64 := by
    rw [output]
    have bound := space.physical
    change reservation.pointer % 2^64 + 8 ≤ 2^64
    rw [Nat.mod_eq_of_lt space.pointerBound]
    omega
  have stackC : 48 ≤ (r (.GPR 31#5) c).toNat := by rw [setupABI.sp]; exact owned.stackBound
  let d := firstCompleted c base
  have firstRun : run 30 c = d := first_run c base (setupABI.code code)
    (setupABI.error.trans error) (setupABI.aligned aligned) setup.1
  have firstPost : FirstPost c d base := first_contract c base stackC physicalOutput
  have firstABI : SmallABI s d := setupABI.trans firstPost.abi
  have firstFrame : MemoryFrame (activeWrites s reservation (SszNative.NatMul.wordWritten operand factor)) c d :=
    first_frame_active reservation _ (by rw [SszNative.NatMul.wordWritten_length]; omega)
      space.pointerBound setupABI output firstPost
  have allFirst : MemoryFrame (writesFor s (outcome s operand factor)) s d := by
    apply currentFrame.trans
    rw [model]
    exact firstFrame.weaken (active_to_full s reservation _)
  have inputD : NatCompare.Words d raw rawWords :=
    NatMul.words_preserve allFirst owned.operandAt.2.2.1 owned.inputOwned owned.scan_words
  have separateD : Protected (NatMul.loopWrites (r (.GPR 31#5) d) pointer (count + 1))
      raw.toNat (8 * rawWords.length) := by
    have inputOwnership : Protected (writesFor s (committed reservation (SszNative.NatMul.wordWritten operand factor)))
        raw.toNat (8 * rawWords.length) := by
      have protection := owned.inputOwned
      change Protected (writesFor s (outcome s operand factor))
        raw.toNat (8 * rawWords.length) at protection
      rw [model] at protection
      exact protection
    have inputProtection := protected_subset inputOwnership
      (loop_writes_subset s d reservation (SszNative.NatMul.wordWritten operand factor)
        space.pointerBound firstABI.sp)
    simpa only [SszNative.NatMul.wordWritten_length] using inputProtection
  have loopSpace : NatMul.LoopSpace (r (.GPR 31#5) d) pointer (count + 1) := by
    simpa only [firstABI.sp] using space.stack
  have head : LoopHeadAt d base operand.pointer pointer factor operand.words count 1 := by
    refine ⟨firstPost.pc, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [firstPost.registers 1#5 (by decide), setup.2.1, currentOwned.pointer]
    · rw [firstPost.registers 2#5 (by decide), Reserve.first_registers u base 2#5 (by decide), currentOwned.payload]
      rfl
    · exact (firstPost.registers 3#5 (by decide)).trans
        ((Reserve.first_registers u base 3#5 (by decide)).trans currentOwned.factorRegister)
    · exact (firstPost.registers 9#5 (by decide)).trans
        ((Reserve.first_registers u base 9#5 (by decide)).trans
          ((prior.frame.registers 9#5 (by decide)).trans countReg))
    · simpa only [Nat.sub_self] using
        (firstPost.registers 13#5 (by decide)).trans setup.2.2.2.1
    · rw [firstPost.registers 15#5 (by decide), setup.2.2.2.2.2.2.1, nextPointer]
  have currentFirst : NatCompare.Words d pointer [operand.words[0]?.getD 0#64 * factor] := by
    simpa only [output, firstLow, operandWords] using firstPost.words
  have carry : r (.GPR 14#5) d = NatMulProduct.high (operand.words[0]?.getD 0#64) factor := by
    rw [firstPost.carry, firstInput, setupABI.registers 3#5 (by decide),
      owned.factorRegister, operandWords]
  have biasD : r (.GPR 8#5) d = -BitVec.ofNat 64 (8 * count) :=
    (firstPost.registers 8#5 (by decide)).trans
      ((Reserve.first_registers u base 8#5 (by decide)).trans
        ((prior.frame.registers 8#5 (by decide)).trans bias))
  obtain ⟨rest, t, ran, returned, image, written, finishFrame⟩ := finish_run d base pointer factor operand
    (firstABI.code code) (firstABI.error.trans error) (firstABI.aligned aligned) head large loopSpace
    owned.operandAt.2.2.1 separateD inputD currentFirst carry biasD
    ((firstPost.registers 10#5 (by decide)).trans output)
    ((firstPost.registers 11#5 (by decide)).trans firstLow)
    ((firstPost.registers 12#5 (by decide)).trans width)
    (allocation_normalize_owned s d operand factor owned reservation firstABI space)
  have suffix : MemoryFrame (activeWrites s reservation (SszNative.NatMul.wordWritten operand factor)) c t := by
    apply firstFrame.trans
    apply finish_frame_active reservation _ space.pointerBound owned.stackBound firstABI
    simpa only [SszNative.NatMul.wordWritten_length] using finishFrame
  have full : MemoryFrame (writesFor s (outcome s operand factor)) s t := by
    apply currentFrame.trans
    rw [model]
    exact suffix.weaken (active_to_full s reservation _)
  have cursorPhysical := owned.arenaBound
  have cursorAddress : (r (.GPR 4#5) s + 16#64).toNat = (r (.GPR 4#5) s).toNat + 16 := by bv_omega
  have sameCursor := suffix.read (r (.GPR 4#5) s + 16#64) 8
    (by rw [cursorAddress]; omega)
    (by rw [cursorAddress]; exact (allocation_header_active s operand factor owned reservation model).subspan 16 8 (by decide))
  have cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat = reservation.used := by
    rw [sameCursor, ← priorFrame.arena, (Reserve.first_memory u base pc
      (by rw [priorFrame.arena, cursorAddress]; omega)).2]
    exact finishReg
  obtain ⟨before, beforeRun⟩ := prior.runs
  refine ⟨before + 7 + 30 + rest, t, ?_, ?_⟩
  · rw [run_plus, run_plus, run_plus, beforeRun, setupRun, firstRun, ran]
  · apply allocation_post s t operand factor owned reservation model
      (firstABI.returned returned) _ written cursor full
    simpa only [firstABI.out] using image

end SszArm.NatMulWord.Large
