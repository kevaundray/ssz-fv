import SszX86.MeasureBitsProgressiveSelect
import SszX86.MeasureBitsProgressiveCommit
import SszX86.MeasureBitsFirstFailure
import SszX86.MeasureBitsControl

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem progressive_count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s t : MachineData) (limit : Option NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.progressiveBitList limit) (.bits bits) buffer address capacity used)
    (memory : t.dmem = s.dmem) (sp : t.regs.rsp = s.regs.rsp)
    (outReg : t.regs.rbx = s.regs.rbx) (headerReg : t.regs.rcx = s.regs.rcx)
    (vectors : t.zmms = s.zmms)
    (selected : t.regs.rax.toBitVec.setWidth 8 &&& 1#8 = if limit.isSome then 1#8 else 0#8)
    (bounded : ∀ cap, limit = some cap → t.regs.rbp.toBitVec = cap.pointer ∧ t.regs.r12.toBitVec = cap.payload)
    (low : t.regs.r15.toBitVec = bits.count.setWidth 64)
    (high : t.regs.r14.toBitVec = (bits.count >>> 64).setWidth 64) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s (.progressiveBitList limit) (.bits bits)
        buffer address capacity used u.1)
      (t, base + 957) := by
  have headerWords := arena_loads s.dmem s.regs.rcx.toBitVec address capacity used owned.arena
  apply progressive_high_cps e base hc
  intro flags
  by_cases small : bits.count.toNat < 2^64
  · have zero := (NatFromU128.wide_small_iff bits.count).1 small
    simp only [high, zero, ↓reduceIte]
    apply progressive_small_cps e base hc
    intro zeroFlags
    have native := NatFromU128.result_model_small address capacity used bits.count small
    change countCall bits address capacity used = _ at native
    apply progressive_select_cps e base hc helpers s _ limit (.small (bits.count.setWidth 64)) bits
      buffer address capacity used owned
    · exact count_prefix_small s _ (.progressiveBitList limit) bits buffer address capacity used
        owned small memory sp outReg vectors
    · simp only [native, NatArithmetic.unchanged]
    · rfl
    · exact low
    · exact selected
    · exact bounded
    · exact headerReg
    · exact low
    · exact high
  · have nonzero : (bits.count >>> 64).setWidth 64 ≠ 0#64 := by
      intro zero
      exact small ((NatFromU128.wide_small_iff bits.count).2 zero)
    simp only [high, nonzero, ↓reduceIte]
    apply eventually_trans (step e)
      (ProgressiveReservation.Post {t with status := flags} base address capacity used) _ _
      (ProgressiveReservation.runs e base hc _ address capacity used
        ⟨by simpa only [memory, headerReg] using headerWords.1,
          by simpa only [memory, headerReg] using headerWords.2.1,
          by simpa only [memory, headerReg] using headerWords.2.2⟩)
    rintro ⟨u, pc⟩ ⟨reservationFrame, branch⟩
    rcases branch with ⟨failed, rfl⟩ | ⟨r, reserved, rfl, readyFlags, rfl⟩
    · apply first_failure_cps e base hc s u (.progressiveBitList limit) limit bits buffer address capacity used owned
        rfl small failed (reservationFrame.memory.trans memory)
      · exact (UInt64.eq_of_toBitVec_eq
          (reservationFrame.registers .rsp (by decide) (by decide) (by decide) (by decide))).trans sp
      · exact (UInt64.eq_of_toBitVec_eq
          (reservationFrame.registers .rbx (by decide) (by decide) (by decide) (by decide))).trans outReg
      · exact reservationFrame.vectors.trans vectors
    · obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
      have pointerWord : address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat) =
          BitVec.ofNat 64 r.pointer := by
        rw [shape]
        simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have cursorWord : BitVec.ofNat 64 (Arena.start address.toNat used.toNat + 16) =
          BitVec.ofNat 64 r.used := by rw [shape]; rfl
      let ready := ProgressiveReservation.Ready {t with status := flags} address used readyFlags
      let committed := ProgressiveReservation.committed ready
      have memoryForm : committed.dmem = vectorCommitMem s r bits.count := by
        simp only [committed, ProgressiveReservation.committed, ready, ProgressiveReservation.Ready,
          vectorCommitMem, memory, headerReg, low, high, UInt64.toBitVec_ofBitVec,
          UInt64.toBitVec_ofNat', pointerWord, cursorWord]
      have resources : CountPrefix s bits address capacity used committed := by
        apply count_prefix_committed s committed (.progressiveBitList limit) bits buffer address capacity used
          owned small r reserved s.dmem
        · intro a outside
          rfl
        · exact mapped_extension_refl _
        · exact memoryForm
        · exact sp
        · exact outReg
        · exact vectors
      have native := NatFromU128.result_model_success address capacity used bits.count small r reserved
      change countCall bits address capacity used = _ at native
      apply ProgressiveReservation.commit_cps e base hc
      · exact ⟨_, by simpa only [ProgressiveReservation.Ready, memory, headerReg] using headerWords.2.2⟩
      · simpa only [ProgressiveReservation.Ready, UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat',
          pointerWord, memory] using reserve_mapped s _ _ buffer address capacity used owned r reserved
      apply progressive_select_cps e base hc helpers s committed limit
        (.large (BitVec.ofNat 64 r.pointer) [bits.count.setWidth 64, (bits.count >>> 64).setWidth 64]) bits
        buffer address capacity used owned resources
      · rw [native]
      · simpa only [committed, ProgressiveReservation.committed, ready, ProgressiveReservation.Ready,
          UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat', NatOperand.pointer] using pointerWord
      · rfl
      · exact selected
      · exact bounded
      · exact headerReg
      · exact low
      · exact high

end SszX86.Measure.Bits
