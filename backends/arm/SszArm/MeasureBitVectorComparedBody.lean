import SszArm.MeasureBitVectorMismatch
import SszArm.MeasureBitVectorSuccess

namespace SszArm.Measure.BitVector

open SszNative (NatOperand)
open SszNative.Serialize (Packed)

theorem pair_equal_iff (s : ArmState) (cap : NatOperand) (bits : Packed)
    (low : r (.GPR 8#5) s = bits.count.setWidth 64)
    (high : r (.GPR 9#5) s = (bits.count >>> 64).setWidth 64)
    (represented : (r (.GPR 10#5) s).toNat + 2^64 * (r (.GPR 11#5) s).toNat = cap.value) :
    (r (.GPR 11#5) s = r (.GPR 9#5) s ∧ r (.GPR 10#5) s = r (.GPR 8#5) s) ↔
      cap.value = bits.count.toNat := by
  have counted := congrArg BitVec.toNat (count_pair bits.count)
  rw [NatToU128.append_toNat] at counted
  rw [← low, ← high] at counted
  constructor
  · rintro ⟨sameHigh, sameLow⟩
    rw [sameHigh, sameLow] at represented
    omega
  · intro equal
    have capLow := (r (.GPR 10#5) s).isLt
    have capHigh := (r (.GPR 11#5) s).isLt
    have countLow := (r (.GPR 8#5) s).isLt
    have countHigh := (r (.GPR 9#5) s).isLt
    exact ⟨BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega)⟩

theorem compared_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bits : Packed)
    (owned : Owned s args (.bitVector cap) (.bits bits)) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3268#64) (descriptor : r (.GPR 1#5) s = args.descriptor + 8#64)
    (low : r (.GPR 8#5) s = bits.count.setWidth 64)
    (high : r (.GPR 9#5) s = (bits.count >>> 64).setWidth 64)
    (represented : (r (.GPR 10#5) s).toNat + 2^64 * (r (.GPR 11#5) s).toNat = cap.value) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.bitVector cap) (.bits bits) base := by
  have stackLow := owned.stackLow
  have safe : 16 ≤ (r (.GPR 31#5) s).toNat := by
    rw [registers.stack, Args.bodySP]
    bv_omega
  let u := compared s base
  have before := compare_run s base code error aligned pc safe
  have frame : CapFrame s u := compared_cap_frame s base safe
  have own := frame.owned owned registers.stack
  have ur : BodyRegisters u args :=
    ⟨(frame.registers 19#5 (by decide)).trans registers.result,
     (frame.registers 20#5 (by decide)).trans registers.arena,
     (frame.registers 21#5 (by decide)).trans registers.value, frame.sp.trans registers.stack⟩
  have semantic := pair_equal_iff s cap bits low high represented
  have readyPC := compared_pc s base
  have branch : ∃ fuel t, run fuel u = t ∧ Produced u t args (.bitVector cap) (.bits bits) base := by
    by_cases equal : cap.value = bits.count.toNat
    · exact success_body u base args cap bits own ur (code.congr frame.program)
        (frame.error.trans error) (frame.aligned aligned)
        (by simpa [semantic, equal] using readyPC) equal
    · exact mismatch_body u base args cap bits own ur (code.congr frame.program)
        (frame.error.trans error) (frame.aligned aligned)
        (by simpa [semantic, equal] using readyPC)
        ((frame.registers 1#5 (by decide)).trans descriptor)
        ((frame.registers 8#5 (by decide)).trans low)
        ((frame.registers 9#5 (by decide)).trans high) equal
  obtain ⟨fuel, t, after, post⟩ := branch
  exact ⟨(compareOps (decide (r (.GPR 11#5) s = r (.GPR 9#5) s))).length + fuel, t,
    by rw [run_plus, before, after], frame.prepend owned registers.stack post⟩

end SszArm.Measure.BitVector
