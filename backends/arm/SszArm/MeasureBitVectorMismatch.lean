import SszArm.MeasureBitVectorAllocateBody
import SszArm.MeasureBitVectorSmallScope

namespace SszArm.Measure.BitVector

open Result
open SszNative (NatOperand)
open SszNative.Serialize (Packed)

private theorem mismatch3320_effect (s : ArmState) :
    p3320.effect s = w .PC
      (if r (.GPR 9#5) s = 0#64 then r .PC s + 4#64 else r .PC s + 12#64) s := by
  change exec_inst (.BR (.Compare_branch { sf := 1, op := 1, imm19 := 3, Rt := 9 })) s = _
  by_cases small : r (.GPR 9#5) s = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, small]

private theorem mismatch3324_effect (s : ArmState) :
    p3324.effect s = w .PC (r .PC s + 4#64) (w (.GPR 10#5) 0#64 s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 10 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem mismatch3328_effect (s : ArmState) :
    p3328.effect s = w .PC (r .PC s + 88#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 22 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

def mismatchOps (small : Bool) : List Op := if small then [p3320, p3324, p3328] else [p3320]

@[irreducible] def mismatchReady (s : ArmState) (base : BitVec 64) : ArmState :=
  if r (.GPR 9#5) s = 0#64 then w .PC (base + 3416#64) (w (.GPR 10#5) 0#64 s)
    else w .PC (base + 3332#64) s

theorem mismatch_run (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (error : read_err s = .None) (pc : read_pc s = base + 3320#64) :
    run (mismatchOps (decide (r (.GPR 9#5) s = 0#64))).length s = mismatchReady s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base (mismatchOps (decide (r (.GPR 9#5) s = 0#64))) s := by
    by_cases small : r (.GPR 9#5) s = 0#64 <;>
      simp (config := {decide := true, instances := true})
        [mismatchOps, Follows, show p3320.offset = 3320 from rfl,
         show p3324.offset = 3324 from rfl, show p3328.offset = 3328 from rfl,
         mismatch3320_effect, mismatch3324_effect,
         state_simp_rules, pc, error, small, BitVec.add_assoc]
  rw [runs _ s base code follows]
  by_cases small : r (.GPR 9#5) s = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [mismatchReady, mismatchOps, effect, mismatch3320_effect, mismatch3324_effect,
       mismatch3328_effect, state_simp_rules, pc, small,
       BitVec.add_assoc, NatExact.gpr_w_pc]

theorem mismatch_frame (s : ArmState) (base : BitVec 64) : CapFrame s (mismatchReady s base) := by
  by_cases small : r (.GPR 9#5) s = 0#64
  all_goals
    constructor
    · simp [mismatchReady, small, state_simp_rules]
    · simp [mismatchReady, small, state_simp_rules]
    · intro reg outside
      have different : reg ≠ 10#5 := fun equal => outside (by simp [equal])
      simp_all [mismatchReady, state_simp_rules]
    · intro reg
      simp [mismatchReady, small, state_simp_rules]
    · intro address outside
      simp [mismatchReady, small, state_simp_rules]

theorem mismatch_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bits : Packed)
    (owned : Owned s args (.bitVector cap) (.bits bits)) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3320#64) (descriptor : r (.GPR 1#5) s = args.descriptor + 8#64)
    (low : r (.GPR 8#5) s = bits.count.setWidth 64)
    (high : r (.GPR 9#5) s = (bits.count >>> 64).setWidth 64)
    (mismatch : cap.value ≠ bits.count.toNat) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.bitVector cap) (.bits bits) base := by
  let u := mismatchReady s base
  have before := mismatch_run s base code error pc
  have frame : CapFrame s u := mismatch_frame s base
  have own := frame.owned owned registers.stack
  have uo := (frame.registers 19#5 (by decide)).trans registers.result
  have us := frame.sp.trans registers.stack
  have ud := (frame.registers 1#5 (by decide)).trans descriptor
  have ul := (frame.registers 8#5 (by decide)).trans low
  have uh := (frame.registers 9#5 (by decide)).trans high
  have branch : ∃ fuel t, run fuel u = t ∧ Produced u t args (.bitVector cap) (.bits bits) base := by
    by_cases zero : r (.GPR 9#5) s = 0#64
    · have small : bits.count.toNat < 2^64 := by
        have countHigh : (bits.count >>> (64 : Nat)).setWidth 64 = 0#64 := high.symm.trans zero
        bv_omega
      exact small_scope_body u base args cap bits own uo us (code.congr frame.program)
        (frame.error.trans error) (frame.aligned aligned)
        (by simp [u, mismatchReady, zero, state_simp_rules]) ud
        (by simp [u, mismatchReady, zero, state_simp_rules]) ul mismatch small
    · exact allocate_body u base args cap bits own uo us
        ((frame.registers 20#5 (by decide)).trans registers.arena) ud ul uh mismatch
        (by simpa only [frame.registers 9#5 (by decide)] using zero)
        (code.congr frame.program) (frame.error.trans error) (frame.aligned aligned)
        (by simp [u, mismatchReady, zero, state_simp_rules])
  obtain ⟨fuel, t, after, post⟩ := branch
  exact ⟨(mismatchOps (decide (r (.GPR 9#5) s = 0#64))).length + fuel, t,
    by rw [run_plus, before, after], frame.prepend owned registers.stack post⟩

end SszArm.Measure.BitVector
