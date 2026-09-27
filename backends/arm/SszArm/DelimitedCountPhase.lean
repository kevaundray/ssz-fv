import SszArm.DelimitedValidation
import SszArm.DelimitedCount

namespace SszArm.Delimited

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem count_start_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (unchanged : reg ∉ [8#5, 9#5, 10#5, 23#5, 31#5]) :
    r (.GPR reg) (block base clzStartOps s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at unchanged
  simp (disch := simp_all) [block, clzStartOps, Op.effect, put, next, state_simp_rules]

private theorem count_end_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (unchanged : reg ∉ [8#5, 9#5, 10#5, 24#5, 26#5, 31#5]) :
    r (.GPR reg) (block base countOps s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at unchanged
  simp (disch := simp_all) [block, countOps, Op.effect, put, next, state_simp_rules]

private theorem count_start_vectors (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (block base clzStartOps s) = r (.SFP reg) s := by
  simp [block, clzStartOps, Op.effect, put, next, state_simp_rules]

private theorem count_end_vectors (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (block base countOps s) = r (.SFP reg) s := by
  simp [block, countOps, Op.effect, put, next, state_simp_rules]

private theorem count_end_memory (s : ArmState) (base : BitVec 64) :
    (block base countOps s).mem = s.mem := by
  simp [block, countOps, Op.effect, put, next, state_simp_rules]

private theorem count_slot_frame (s : ArmState) (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s (countSlot s) := by
  intro a outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
  simp (disch := delimited_side) [countSlot, BoolCodec.write_mem_bytes_frame]

/-- The count phase only reuses the one true lowering slot below the saved96. -/
theorem lower_frame_local {s u t : ArmState}
    (nonempty : r (.GPR 3#5) s ≠ 0#64)
    (stack : 112 ≤ (r (.GPR 31#5) s).toNat)
    (sp : r (.GPR 31#5) u = r (.GPR 31#5) s - 96#64)
    (frame : MemoryFrame [((r (.GPR 31#5) u).toNat - 16, 16)] u t) :
    MemoryFrame (localWrites s) u t := by
  have spNat : (r (.GPR 31#5) u).toNat = (r (.GPR 31#5) s).toNat - 96 := by bv_omega
  intro a outside
  apply frame a
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst span
  have apart := outside (activationSpan s) (by simp [localWrites])
  simp only [activationSpan, nonempty, ↓reduceIte] at apart
  simp only [spNat]
  omega

/-- Native post-count checkpoint. The model words, not another semantic count
implementation, are the interface to reservation and optional comparison. -/
structure Counted (s t : ArmState) (base : BitVec 64) (limit : Option Nat)
    (data : Ssz.Bytes) : Prop where
  program : t.program = s.program
  error : read_err t = .None
  aligned : CheckSPAlignment t
  saved : Saved s t
  arguments : ∀ reg : BitVec 5, reg ∈ [0#5, 1#5, 2#5, 3#5, 4#5] →
    r (.GPR reg) t = r (.GPR reg) s
  preceding : r (.GPR 25#5) t = BitVec.ofNat 64 (data.size - 1)
  counter : r (.GPR 26#5) t = BitVec.ofNat 64 (7 - Ssz.highestBit data[data.size - 1]!)
  low : r (.GPR 24#5) t =
    (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)).low
  high : r (.GPR 23#5) t =
    (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)).high
  pc : read_pc t = if
      (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)).high = 0#64
    then base + 148#64 else base + 268#64
  frame : MemoryFrame (localWrites s) s t
  inputs : InputsPreserved s t limit data

/-- The loop fuel follows the checked byte/CLZ bound; the original activation
and arguments survive the lowering save, actual loop, and count exit. -/
theorem count_phase (s u : ArmState) (base : BitVec 64) (limit : Option Nat)
    (data : Ssz.Bytes) (owned : Owned s limit data) (started : Started s u base limit data)
    (hc : CodeAt s base) (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0) :
    ∃ t, run (10 + 3 * (25 + Ssz.highestBit data[data.size - 1]!) + 8) u = t ∧
      Counted s t base limit data := by
  let byte := data[data.size - 1]!
  let a := block base clzStartOps u
  have nonzero : r (.GPR 3#5) s ≠ 0#64 := by
    have length := owned.length
    bv_omega
  have stack : 112 ≤ (r (.GPR 31#5) s).toNat := by
    simpa only [activationSpan, nonzero, ↓reduceIte] using owned.stackBound
  have stackU : 16 ≤ (r (.GPR 31#5) u).toNat := by
    have sp := started.saved.sp
    bv_omega
  have codeU : CodeAt u base := by simpa only [CodeAt, started.program] using hc
  have first : run 10 u = a := clzStart_run u base codeU started.error started.aligned
    (by simpa only [delimiter, ↓reduceIte] using started.pc)
  have byteWord : r (.GPR 8#5) u = BitVec.ofNat 64 byte.toNat := by
    rw [started.byte]
    apply BitVec.eq_of_toNat_eq
    simp only [byte, BitVec.toNat_setWidth, UInt8.toNat_toBitVec, BitVec.toNat_ofNat]
  have initial := clz_start_registers u base byte delimiter byteWord
  have codeA : CodeAt a base := by simpa only [a, CodeAt, block_program] using codeU
  have errorA : read_err a = .None := (block_error base clzStartOps u).trans started.error
  have alignA : CheckSPAlignment a := block_aligned base clzStartOps u started.aligned
  obtain ⟨v, loop, loopFrame, loopMemory, loopPc, loopCounter⟩ :=
    clz_byte a base byte codeA errorA alignA initial.1 delimiter initial.2.1 initial.2.2.1
  let t := block base countOps v
  have lengthWord : r (.GPR 3#5) s = BitVec.ofNat 64 data.size := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt owned.physical, owned.length]
  have inputLength : r (.GPR 3#5) v = BitVec.ofNat 64 data.size := by
    rw [loopFrame.registers 3#5 (by decide), count_start_register u base 3#5 (by decide),
      started.arguments 3#5 (by simp)]
    exact lengthWord
  have prefixU : r (.GPR 25#5) u = BitVec.ofNat 64 (data.size - 1) := by
    have prefixState := started.preceding
    have length := owned.length
    bv_omega
  have prefixV : r (.GPR 25#5) v = BitVec.ofNat 64 (data.size - 1) := by
    rw [loopFrame.registers 25#5 (by decide), count_start_register u base 25#5 (by decide)]
    exact prefixU
  have loopSp : r (.GPR 31#5) v = r (.GPR 31#5) a := by
    simpa only [BitVec.ofNat_eq_ofNat] using loopFrame.sp
  have threshold : read_mem_bytes 8 (r (.GPR 31#5) v) v = countThreshold := by
    rw [loopSp, (Memory.mem_eq_iff_read_mem_bytes_eq.mp loopMemory) 8]
    exact (clz_start_saved u base stackU).1
  have values := count_exit v base byte data.size owned.physical inputLength prefixV loopCounter threshold
  have executed : run 8 v = t := count_run v base
    (by simpa only [CodeAt, loopFrame.program] using codeA)
    (loopFrame.error.trans errorA) (loopFrame.aligned alignA) loopPc
  have sp : r (.GPR 31#5) t = r (.GPR 31#5) u := by
    rw [values.2.2.1, loopSp, initial.2.2.2.2.2.2]
    exact BitVec.sub_add_cancel _ _
  have memory : MemoryFrame [((r (.GPR 31#5) u).toNat - 16, 16)] u t := by
    have same := (count_end_memory v base).trans (loopMemory.trans (clz_start_memory u base))
    intro address outside
    rw [congrFun same address]
    exact count_slot_frame u stackU address outside
  have localMemory := lower_frame_local nonzero stack started.saved.sp memory
  have frame := started.frame.trans localMemory
  have vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) u := by
    intro reg
    exact (count_end_vectors v base reg).trans
      ((loopFrame.vectors reg).trans (count_start_vectors u base reg))
  have saved : Saved s t := started.saved.frame memory sp (by
      have original := (r (.GPR 31#5) s).isLt
      have savedSp := started.saved.sp
      bv_omega) (by
      right
      intro span member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst span
      omega) (by
      intro reg low high
      exact congrArg (BitVec.setWidth 64) (vectors reg))
  have arguments : ∀ reg : BitVec 5, reg ∈ [0#5, 1#5, 2#5, 3#5, 4#5] →
      r (.GPR reg) t = r (.GPR reg) s := by
    intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      rw [count_end_register _ _ _ (by decide), loopFrame.registers _ (by decide),
        count_start_register _ _ _ (by decide)] <;>
      exact started.arguments _ (by simp)
  have high : r (.GPR 23#5) t =
      (SszNative.Delimited.countWords data.size (Ssz.highestBit byte)).high := by
    rw [count_end_register v base 23#5 (by decide), loopFrame.registers 23#5 (by decide),
      initial.2.2.2.1, prefixU]
    rfl
  have low : r (.GPR 24#5) t =
      (SszNative.Delimited.countWords data.size (Ssz.highestBit byte)).low := by
    rw [values.1]
    simp [SszNative.Delimited.countWords, BitVec.ofNat_add, BitVec.ofNat_mul, Nat.mul_comm]
  have smallIff :
      (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)).high = 0#64 ↔
        ¬ 2^61 < data.size := by
    rw [SszNative.Delimited.CountWords.high_zero_iff,
      SszNative.Delimited.countWords_data_value data owned.physical]
    constructor
    · intro small tooLong
      exact Nat.not_le_of_lt small ((SszNative.BitView.delimited_count_large data).mpr tooLong)
    · intro notLong
      exact Nat.lt_of_not_le (fun large =>
        notLong ((SszNative.BitView.delimited_count_large data).mp large))
  refine ⟨t, ?_, ?_⟩
  · rw [run_plus, run_plus, first, loop, executed]
  · refine ⟨?_, ?_, ?_, saved, arguments, ?_, values.2.1, low, high, ?_, frame,
      inputs_preserved owned (local_frame (SszNative.Delimited.allocation data (arenaOf s)) frame)⟩
    · exact (block_program base countOps v).trans
        (loopFrame.program.trans ((block_program base clzStartOps u).trans started.program))
    · exact (block_error base countOps v).trans (loopFrame.error.trans errorA)
    · exact block_aligned base countOps v (loopFrame.aligned alignA)
    · rw [count_end_register v base 25#5 (by decide)]
      exact prefixV
    · rw [values.2.2.2]
      by_cases long : 2^61 < data.size
      · have highNonzero :
            (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)).high ≠ 0#64 :=
          fun zero => smallIff.mp zero long
        simp only [long, highNonzero, ↓reduceIte]
      · simp only [long, smallIff.mpr long, ↓reduceIte]

end SszArm.Delimited
