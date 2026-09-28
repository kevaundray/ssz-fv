import SszArm.MeasureBitsAllocObserve

namespace SszArm.Measure.Bits.Alloc

open UintCodec (widthLoad)

/-- The original three inlined two-limb constructors, including every failed
check and every committed allocation. The input cursor need not be valid. -/
theorem constructor_executes (site : Site) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 site.entry)
    (large : r (.GPR site.highReg) s ≠ 0#64) (input : Input s) :
    ∃ fuel t, run fuel s = t ∧ ConstructorPost site s t base := by
  obtain ⟨fuel, u, before, reached, branch⟩ :=
    checks_runs site s base (addressWord s) (capacityWord s) (usedWord s)
      code error aligned pc rfl rfl rfl
  rcases branch with ⟨failed, failedPC⟩ | ⟨checks, commitPC, address, start, finish⟩
  · have model := outcome_failure site s large failed
    refine ⟨fuel, u, before, reached.frame.program, reached.frame.error, ?_,
      reached.frame.vectors, ?_, ?_, ?_, ?_, ?_⟩
    · intro reg keep
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at keep
      apply reached.frame.registers reg
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨keep.1, keep.2.1, keep.2.2.1, keep.2.2.2.1⟩
    · simp only [model, SszNative.NatArithmetic.unchanged]
      exact ⟨True.intro, failedPC⟩
    · simp only [model, SszNative.NatArithmetic.unchanged]
      rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp reached.frame.memory]
      rfl
    · constructor
      · exact Memory.mem_eq_iff_read_mem_bytes_eq.mp reached.frame.memory _ _
      · exact Memory.mem_eq_iff_read_mem_bytes_eq.mp reached.frame.memory _ _
    · simp [NatDivision.WrittenAt, model, SszNative.NatArithmetic.unchanged]
    · intro address outside
      exact congrFun reached.frame.memory address
  · obtain ⟨space, pointerNat⟩ := input.commitSpace reached checks address start
    let t := commitResult site u base
    have after : run 4 u = t := commit_run site u base (code.congr reached.frame.program)
      (reached.frame.error.trans error) (reached.frame.aligned aligned) commitPC
    have model := outcome_wide site s large checks
    have headerReg := reached.frame.registers 20#5 (by cases site <;> decide)
    have low := reached.frame.registers site.lowReg (by cases site <;> decide)
    have high := reached.frame.registers site.highReg (by cases site <;> decide)
    have pointer : allocatedPointer site u = BitVec.ofNat 64
        ((addressWord s).toNat + SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat) := by
      apply BitVec.eq_of_toNat_eq
      rw [pointerNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have bound := space.payload
      rw [pointerNat] at bound
      omega
    have observed := commit_at site u base space
    have words := commit_words site u base space
    have pair := commit_pair site u base
    refine ⟨fuel + 4, t, by rw [run_plus, before, after],
      (commit_program site u base).trans reached.frame.program,
      (commit_error site u base).trans reached.frame.error, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro reg keep
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at keep
      have notPointer : reg ≠ site.pointerReg := keep.2.2.2.2.1
      have notCount : reg ≠ site.countReg := keep.2.2.2.2.2
      apply (commit_register site u base reg notPointer notCount).trans
      apply reached.frame.registers reg
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨keep.1, keep.2.1, keep.2.2.1, keep.2.2.2.1⟩
    · intro reg
      exact (commit_vector site u base reg).trans (reached.frame.vectors reg)
    · simp only [model]
      refine ⟨commit_pc site u base, ?_, ?_, ?_⟩
      · simpa only [SszNative.NatOperand.pointer, pointer] using pair.1
      · simpa only [SszNative.NatOperand.payload, List.length_cons, List.length_nil] using pair.2
      · simpa only [pointer, low, high] using observed
    · simp only [model]
      rw [← headerReg, commit_cursor site u base space]
      exact finish
    · have header := commit_header site u base space
      have baseRead : addressWord u = addressWord s := by
        unfold addressWord
        rw [headerReg]
        exact Memory.mem_eq_iff_read_mem_bytes_eq.mp reached.frame.memory _ _
      have capacityRead : capacityWord u = capacityWord s := by
        unfold capacityWord
        rw [headerReg]
        exact Memory.mem_eq_iff_read_mem_bytes_eq.mp reached.frame.memory _ _
      simpa only [headerReg, baseRead, capacityRead] using header
    · intro reservation allocated
      simp only [model, Option.some.injEq] at allocated
      subst reservation
      simpa only [t, model, pointerNat, low, high] using words
    · have framed := commit_frame site u base space.header space.payload
      intro address outside
      have last := framed address (by
        simpa only [writesFor, model, headerReg, pointerNat] using outside)
      exact last.trans (congrFun reached.frame.memory address)

end SszArm.Measure.Bits.Alloc
