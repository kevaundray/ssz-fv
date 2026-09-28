import SszArm.MeasureUintOwned
import SszArm.MeasureUintValueScan
import SszArm.MeasureUintCountSmall
import SszArm.MeasureUintCountLarge
import SszSerializeMeasure

namespace SszArm.Measure.Uint

open SszNative (NatOperand)
open SszNative.Limbs

/-- Every physical Nat representation reaches the actual descriptor load with
its exact byte requirement. This includes empty Large and arbitrary high zeros. -/
theorem number_required (s : ArmState) (args : Args) (uintCap number : NatOperand)
    (base : BitVec 64) (owned : Owned s args (.uint uintCap) (.uint number))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 356#64) (registers : BodyRegisters s args) :
    ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
      read_pc t = base + 2736#64 ∧
      pairValue (r (.GPR 8#5) t) (r (.GPR 9#5) t) =
        SszNative.Serialize.requiredBytes number.value := by
  have pair := number_pair owned
  have safe := body_stack_safe owned registers.stack
  have pc' : r .PC s = base + 356#64 := pc
  cases number with
  | small limbWord =>
    let ops : List ValueOp := [.p356, .p360]
    let u := valueBlock base ops s
    have follows : ValueFollows base ops s := by
      simp [ops, ValueFollows, ValueOp.row, ValueOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, pc', BitVec.add_assoc]
    have executed : run 2 s = u := value_run base ops s code error aligned follows
    have frame : NatNarrow.Frame s u := value_pure_frame base _ s (by decide)
    have nextPC : read_pc u = base + 2192#64 := by
      simp [u, ops, valueBlock, ValueOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules, registers.value, pair.1, NatOperand.pointer]
    have loaded : r (.GPR 8#5) u = limbWord := by
      simp [u, ops, valueBlock, ValueOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules, registers.value, pair.2, NatOperand.payload]
    obtain ⟨extra, t, countRun, countFrame, countPC, required⟩ := small_count u base
      (code.congr frame.program) (frame.error.trans error) (frame.aligned aligned)
      nextPC (by simpa only [frame.sp] using safe)
    refine ⟨2 + extra, t, ?_, frame.trans countFrame, countPC, ?_⟩
    · rw [run_plus, executed, countRun]
    · simpa [loaded, NatOperand.value, NatOperand.words, SszNative.Limbs.value] using required
  | large pointer words =>
    have input := owned.operand_at (.large pointer words)
      (by simp [Emit.descriptorOperands, Emit.valueOperands])
    have nonnull : pointer ≠ 0#64 := by
      intro zero
      have positive := input.1
      simp [zero] at positive
    have source := operand_source owned registers.stack pointer words (by simp)
    have memory := operand_words owned pointer words (by simp)
    let ops : List ValueOp := [.p356, .p360, .p364]
    let u := valueBlock base ops s
    have follows : ValueFollows base ops s := by
      simp [ops, ValueFollows, ValueOp.row, ValueOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, pc', BitVec.add_assoc, registers.value,
        pair.1, NatOperand.pointer, nonnull]
    have executed : run 3 s = u := value_run base ops s code error aligned follows
    have frame : NatNarrow.Frame s u := value_pure_frame base _ s (by decide)
    have nextPC : read_pc u = base + 368#64 := by
      simp [u, ops, valueBlock, ValueOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules, registers.value, pair.1, NatOperand.pointer, nonnull, BitVec.add_assoc]
    have pointerReg : r (.GPR 9#5) u = pointer - 8#64 := by
      simp [u, ops, valueBlock, ValueOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules, registers.value, pair.1, NatOperand.pointer]
    have countReg : r (.GPR 8#5) u = BitVec.ofNat 64 words.length := by
      simp [u, ops, valueBlock, ValueOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules, registers.value, pair.2, NatOperand.payload]
    obtain ⟨scanFuel, v, scanRun, scanFrame, _, scanPC, scanZero, scanTop⟩ :=
      value_scan base pointer words words.length u (Nat.le_refl _)
        (code.congr frame.program) (frame.error.trans error) (frame.aligned aligned)
        nextPC pointerReg countReg (frame.source _ _ source) (frame.words _ _ source memory)
    have fullFrame : NatNarrow.Frame s v := frame.trans scanFrame
    have fullRun : run (3 + scanFuel) s = v := by rw [run_plus, executed, scanRun]
    change read_pc v = base + BitVec.ofNat 64 (if sigWords words = 0 then 2732 else 416) at scanPC
    by_cases zero : sigWords words = 0
    · have zeroReg : r (.GPR 8#5) v = 0#64 := scanZero zero
      have zeroPC : read_pc v = base + 2732#64 := by simpa only [if_pos zero] using scanPC
      let t := valueBlock base [.p2732] v
      have zeroFollows : ValueFollows base [.p2732] v := ⟨zeroPC, trivial⟩
      have zeroRun : run 1 v = t := value_run base [.p2732] v (code.congr fullFrame.program)
        (fullFrame.error.trans error) (fullFrame.aligned aligned) zeroFollows
      refine ⟨3 + scanFuel + 1, t, ?_,
        fullFrame.trans (value_pure_frame base _ v (by decide)), ?_, ?_⟩
      · rw [run_plus, fullRun, zeroRun]
      · have zeroPC' : r .PC v = base + 2732#64 := zeroPC
        simp [t, valueBlock, ValueOp.effect, put, next, Emit.Dispatch.next,
          state_simp_rules, zeroPC', BitVec.add_assoc]
      · simp [t, valueBlock, ValueOp.effect, put, next, Emit.Dispatch.next,
          state_simp_rules, zeroReg, pairValue, NatOperand.value, NatOperand.words,
          SszNative.Serialize.requiredBytes_zero_significant words zero]
    · have positive : 0 < sigWords words := by omega
      obtain ⟨count, limb⟩ := scanTop zero
      change r (.GPR 10#5) v = BitVec.ofNat 64 (sigWords words) at count
      change r (.GPR 11#5) v = words[sigWords words - 1]?.getD 0#64 at limb
      have bound : sigWords words < 2^64 := by
        have := sigWords_le_length words
        have := source.2.1
        omega
      have countNat : (r (.GPR 10#5) v).toNat = sigWords words := by
        rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
      have nonzeroPC : read_pc v = base + 416#64 := by simpa only [if_neg zero] using scanPC
      obtain ⟨extra, t, countRun, countFrame, countPC, required⟩ := large_count v base
        (code.congr fullFrame.program) (fullFrame.error.trans error) (fullFrame.aligned aligned)
        nonzeroPC (by simpa only [fullFrame.sp] using safe) (by rw [countNat]; exact positive)
      have topNonzero : (words[sigWords words - 1]?.getD 0#64).toNat ≠ 0 := by
        intro topZero
        apply SszNative.Serialize.significant_top_nonzero words words.length positive
        change words[sigWords words - 1]?.getD 0#64 = 0#64
        exact BitVec.eq_of_toNat_eq (by simpa using topZero)
      refine ⟨3 + scanFuel + extra, t, ?_, fullFrame.trans countFrame, countPC, ?_⟩
      · rw [run_plus, fullRun, countRun]
      · rw [required, countNat, limb]
        simp only [NatOperand.value, NatOperand.words,
          SszNative.Serialize.requiredBytes_significant words positive,
          SszNative.Serialize.bitLength, topNonzero, ↓reduceIte]
        congr 1

end SszArm.Measure.Uint
