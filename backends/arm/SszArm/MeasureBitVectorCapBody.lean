import SszArm.MeasureBitVectorComparedBody

namespace SszArm.Measure.BitVector

open SszNative (NatOperand)
open SszNative.Serialize (Packed)
open SszNative.Limbs (sigWords)

theorem cap_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bits : Packed)
    (owned : Owned s args (.bitVector cap) (.bits bits)) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (if cap.pointer = 0#64 then 3268 else 588))
    (descriptor : r (.GPR 1#5) s = args.descriptor + 8#64)
    (ptr : r (.GPR 11#5) s = cap.pointer) (payload : r (.GPR 10#5) s = cap.payload)
    (low : r (.GPR 8#5) s = bits.count.setWidth 64)
    (high : r (.GPR 9#5) s = (bits.count >>> 64).setWidth 64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.bitVector cap) (.bits bits) base := by
  cases cap with
  | small scalar =>
    exact compared_body s base args (.small scalar) bits owned registers code error aligned
      (by simpa only [NatOperand.pointer, ↓reduceIte] using pc) descriptor low high
      (by simp [ptr, payload, NatOperand.pointer, NatOperand.payload, NatOperand.value,
        NatOperand.words, SszNative.Limbs.value])
  | large pointer words =>
    have input := owned.operand_at (.large pointer words)
      (by simp [Emit.descriptorOperands, Emit.valueOperands])
    have borrowed := owned.operandOwned (.large pointer words)
      (by simp [Emit.descriptorOperands, Emit.valueOperands])
    have stackLow := owned.stackLow
    have position : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 288 := by
      rw [registers.stack, Args.bodySP]
      bv_omega
    have safe : 16 ≤ (r (.GPR 31#5) s).toNat := by
      rw [registers.stack, Args.bodySP]
      bv_omega
    have nonzero : pointer ≠ 0#64 := by have positive := input.1; bv_omega
    have source := NatNarrow.large_source s pointer words
      (writesFor args (outcome s args (.bitVector (.large pointer words)) (.bits bits)))
      input borrowed (by simp [position, writesFor, localWrites, stackWrites, bodyStackWrites]) safe
    have stored := NatNarrow.large_words s pointer words input
    let start := scanStartResult s base
    have before : run 1 s = start := scan_start_run s base code error
      (by simpa [NatOperand.pointer, nonzero] using pc)
    have startFrame : CapFrame s start := scan_start_frame s base
    have pointerStart : r (.GPR 11#5) start = pointer := by
      simpa [start, scanStartResult, NatOperand.pointer, state_simp_rules] using ptr
    have countStart : r (.GPR 10#5) start = BitVec.ofNat 64 words.length := by
      simpa [start, scanStartResult, NatOperand.payload, state_simp_rules] using payload
    have indexStart : r (.GPR 13#5) start = BitVec.ofNat 64 words.length - 1#64 := by
      simp [start, scanStartResult, state_simp_rules, payload, NatOperand.payload]
    obtain ⟨fuel, u, scanned, scanFrame, nextPC, represented⟩ := cap_scanned_ready start base pointer words
      (code.congr startFrame.program) (startFrame.error.trans error) (startFrame.aligned aligned)
      (by simp [start, scanStartResult, state_simp_rules]) pointerStart countStart indexStart
      (startFrame.source _ _ source) (startFrame.words _ _ source stored)
    have frame := startFrame.trans scanFrame
    have own := frame.owned owned registers.stack
    have ur : BodyRegisters u args :=
      ⟨(frame.registers 19#5 (by decide)).trans registers.result,
       (frame.registers 20#5 (by decide)).trans registers.arena,
       (frame.registers 21#5 (by decide)).trans registers.value, frame.sp.trans registers.stack⟩
    have ud := (frame.registers 1#5 (by decide)).trans descriptor
    have ul := (frame.registers 8#5 (by decide)).trans low
    have uh := (frame.registers 9#5 (by decide)).trans high
    have branch : ∃ extra t, run extra u = t ∧
        Produced u t args (.bitVector (.large pointer words)) (.bits bits) base := by
      by_cases wide : 2 < sigWords words
      · have mismatch : (NatOperand.large pointer words).value ≠ bits.count.toNat := by
          have huge := SszNative.Serialize.wide_width_bound words wide
          have countBound := bits.count.isLt
          change SszNative.Limbs.value words ≠ bits.count.toNat
          omega
        exact mismatch_body u base args (.large pointer words) bits own ur
          (code.congr frame.program) (frame.error.trans error) (frame.aligned aligned)
          (by simpa only [wide, ↓reduceIte] using nextPC) ud ul uh mismatch
      · exact compared_body u base args (.large pointer words) bits own ur
          (code.congr frame.program) (frame.error.trans error) (frame.aligned aligned)
          (by simpa only [wide, ↓reduceIte] using nextPC) ud ul uh (represented (by omega))
    obtain ⟨extra, t, after, post⟩ := branch
    exact ⟨1 + fuel + extra, t, by rw [run_plus, run_plus, before, scanned, after],
      frame.prepend owned registers.stack post⟩

end SszArm.Measure.BitVector
