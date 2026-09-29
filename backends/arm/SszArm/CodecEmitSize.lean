import SszArm.CodecEmitSizeFinishOps

namespace SszArm.Codec.Emit.Size

open SszNative (NatOperand)
open SszNative.Limbs SszArm.Emit.Uint

private theorem load_low (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (code : Linked.EmitParts.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 264#64) (address : r (.GPR 8#5) s = pointer)
    (nonempty : 0 < words.length) (stored : NatCompare.Words s pointer words)
    (bound : value words < 2^64) :
    ∃ t, run 1 s = t ∧ Frame s t ∧ read_pc t = base + 268#64 ∧
      r (.GPR 19#5) t = BitVec.ofNat 64 (value words) := by
  have low : read_mem_bytes 8 pointer s = BitVec.ofNat 64 (value words) := by
    have first := stored ⟨0, nonempty⟩
    have limb : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
      simpa [List.getElem?_eq_getElem nonempty] using first
    exact limb.trans (low_word_of_representable words bound)
  let t := block base [.p264] s
  refine ⟨t, runs base [.p264] s code error aligned ⟨pc, trivial⟩,
    block_frame base _ s, ?_, ?_⟩
  · change r .PC s = _ at pc
    simp [t, block, Op.effect, put, next, SszArm.Emit.Dispatch.next,
      state_simp_rules, pc, BitVec.add_assoc]
  · simp [t, block, Op.effect, put, next, SszArm.Emit.Dispatch.next,
      state_simp_rules, address, low]

/-- A representable borrowed size is converted by the actual backward scan and
its native exit branches, including empty and arbitrarily padded zero limbs. -/
theorem scanned_large_correct (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (code : Linked.EmitParts.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 192#64) (address : r (.GPR 8#5) s = pointer)
    (count : r (.GPR 19#5) s = BitVec.ofNat 64 words.length)
    (position : r (.GPR 10#5) s = BitVec.ofNat 64 words.length - 1#64)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words)
    (bound : value words < 2^64) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ read_pc t = base + 268#64 ∧
      r (.GPR 19#5) t = BitVec.ofNat 64 (value words) := by
  have significant : sigWords words ≤ 1 := by
    have fits := ((NatOperand.large pointer words).wordCount_le_iff_value_lt 1).2
      (by simpa [NatOperand.value, NatOperand.words] using bound)
    exact fits
  obtain ⟨fuel, u, runScan, narrow, pointerU, pcU, indexU⟩ :=
    SizeScan.significant_scan base pointer words words.length s (Nat.le_refl _)
      code error aligned pc address position source stored
  have frame := Frame.of_narrow narrow
  have codeU := SizeScan.frame_code narrow code
  have errorU := narrow.error.trans error
  have alignedU := narrow.aligned aligned
  have countU : r (.GPR 19#5) u = BitVec.ofNat 64 words.length :=
    (narrow.registers _ (by decide)).trans count
  have storedU := narrow.words pointer words source stored
  have countBound : words.length < 2^64 := by have limit := source.2.1; omega
  change read_pc u = base + BitVec.ofNat 64 (if sigWords words = 0 then 260 else 244) at pcU
  change sigWords words ≠ 0 → r (.GPR 9#5) u = BitVec.ofNat 64 (sigWords words - 1) at indexU
  by_cases zero : sigWords words = 0
  · have upc : read_pc u = base + 260#64 := by simpa [zero] using pcU
    let v := block base [.p260] u
    have runBranch : run 1 u = v := runs base [.p260] u codeU errorU alignedU ⟨upc, trivial⟩
    have branchFrame : NatNarrow.Frame u v := block_narrow base _ u (by decide)
    by_cases empty : words.length = 0
    · have nil : words = [] := List.length_eq_zero_iff.mp empty
      refine ⟨fuel + 1, v, ?_, frame.trans (Frame.of_narrow branchFrame), ?_, ?_⟩
      · rw [run_plus, runScan, runBranch]
      · simp [v, block, Op.effect, state_simp_rules, countU, empty]
      · simp [v, block, Op.effect, state_simp_rules, countU, nil, value]
    · have positive : 0 < words.length := by omega
      have countNonzero : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
      have pcV : read_pc v = base + 264#64 := by
        simp [v, block, Op.effect, state_simp_rules, countU, countNonzero]
      have pointerV : r (.GPR 8#5) v = pointer := by
        simpa [v, block, Op.effect, state_simp_rules] using pointerU
      obtain ⟨t, runLoad, loadFrame, pcT, valueT⟩ := load_low v base pointer words
        (SizeScan.frame_code branchFrame codeU) (branchFrame.error.trans errorU)
        (branchFrame.aligned alignedU) pcV pointerV positive
        (branchFrame.words pointer words (narrow.source _ _ source) storedU) bound
      refine ⟨fuel + 1 + 1, t, ?_, (frame.trans (Frame.of_narrow branchFrame)).trans loadFrame,
        pcT, valueT⟩
      rw [run_plus, run_plus, runScan, runBranch, runLoad]
  · have one : sigWords words = 1 := by omega
    have positive : 0 < words.length := by have limit := sigWords_le_length words; omega
    have upc : read_pc u = base + 244#64 := by simpa [zero] using pcU
    have indexZero : r (.GPR 9#5) u = 0#64 := by simpa [one] using indexU zero
    let ops : List Op := [.p244, .p248, .p252]
    let v := block base ops u
    have follows : Follows base ops u := by
      change r .PC u = _ at upc
      simp (config := {decide := true, instances := true})
        [ops, Follows, Op.row, Op.effect, put, next, SszArm.Emit.Dispatch.next,
          SszArm.Emit.Dispatch.compare64, state_simp_rules, bitvec_rules, minimal_theory,
          upc, indexZero, BitVec.add_assoc]
    have runBranch : run 3 u = v := runs base ops u codeU errorU alignedU follows
    have branchFrame : NatNarrow.Frame u v := block_narrow base ops u (by decide)
    have pcV : read_pc v = base + 264#64 := by
      simp (config := {decide := true, instances := true})
        [v, ops, block, Op.effect, put, next, SszArm.Emit.Dispatch.next,
          SszArm.Emit.Dispatch.compare64, state_simp_rules, bitvec_rules, minimal_theory,
          indexZero]
    have pointerV : r (.GPR 8#5) v = pointer := by
      simpa [v, ops, block, Op.effect, put, next, SszArm.Emit.Dispatch.next,
        SszArm.Emit.Dispatch.compare64, state_simp_rules] using pointerU
    obtain ⟨t, runLoad, loadFrame, pcT, valueT⟩ := load_low v base pointer words
      (SizeScan.frame_code branchFrame codeU) (branchFrame.error.trans errorU)
      (branchFrame.aligned alignedU) pcV pointerV positive
      (branchFrame.words pointer words (narrow.source _ _ source) storedU) bound
    refine ⟨fuel + 3 + 1, t, ?_, (frame.trans (Frame.of_narrow branchFrame)).trans loadFrame,
      pcT, valueT⟩
    rw [run_plus, run_plus, runScan, runBranch, runLoad]

/-- Small representation takes its real null-pointer branch without reading a limb. -/
theorem small_correct (s : ArmState) (base word : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 184#64)
    (small : r (.GPR 8#5) s = 0#64) (payload : r (.GPR 19#5) s = word) :
    ∃ t, run 1 s = t ∧ Frame s t ∧ read_pc t = base + 268#64 ∧ r (.GPR 19#5) t = word := by
  let t := block base [.p184] s
  refine ⟨t, runs base [.p184] s code error aligned ⟨pc, trivial⟩,
    block_frame base _ s, ?_, ?_⟩
  all_goals simp [t, block, Op.effect, state_simp_rules, small, payload]

/-- Borrowed representation takes the non-null branch and initializes the full
allocated count; the loop itself establishes significant width. -/
theorem large_correct (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (code : Linked.EmitParts.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 184#64) (address : r (.GPR 8#5) s = pointer)
    (nonnull : pointer ≠ 0#64) (count : r (.GPR 19#5) s = BitVec.ofNat 64 words.length)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words)
    (bound : value words < 2^64) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ read_pc t = base + 268#64 ∧
      r (.GPR 19#5) t = BitVec.ofNat 64 (value words) := by
  let u := block base [.p184, .p188] s
  have follows : Follows base [.p184, .p188] s := by
    change r .PC s = _ at pc
    simp [Follows, Op.row, Op.effect, put, next, SszArm.Emit.Dispatch.next,
      state_simp_rules, pc, address, nonnull, BitVec.add_assoc]
  have runEntry : run 2 s = u := runs base [.p184, .p188] s code error aligned follows
  have entryFrame : NatNarrow.Frame s u := block_narrow base _ s (by decide)
  have pcU : read_pc u = base + 192#64 := by
    simp [u, block, Op.effect, put, next, SszArm.Emit.Dispatch.next,
      state_simp_rules, address, nonnull, BitVec.add_assoc]
  have pointerU : r (.GPR 8#5) u = pointer := by
    simpa [u, block, Op.effect, put, next, SszArm.Emit.Dispatch.next, state_simp_rules] using address
  have countU : r (.GPR 19#5) u = BitVec.ofNat 64 words.length :=
    (entryFrame.registers _ (by decide)).trans count
  have positionU : r (.GPR 10#5) u = BitVec.ofNat 64 words.length - 1#64 := by
    simp [u, block, Op.effect, put, next, SszArm.Emit.Dispatch.next, state_simp_rules, count]
  obtain ⟨fuel, t, runScan, scanFrame, pcT, valueT⟩ := scanned_large_correct u base pointer words
    (SizeScan.frame_code entryFrame code) (entryFrame.error.trans error)
    (entryFrame.aligned aligned) pcU pointerU countU positionU
    (entryFrame.source _ _ source) (entryFrame.words _ _ source stored) bound
  refine ⟨2 + fuel, t, ?_, (Frame.of_narrow entryFrame).trans scanFrame, pcT, valueT⟩
  rw [run_plus, runEntry, runScan]

end SszArm.Codec.Emit.Size
