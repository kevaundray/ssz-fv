import SszArm.CodecSerializeMeasured
import SszArm.CodecSerializeReturn
import SszArm.SerializeFinishMeasure

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value)
open Delimited (Protected)

 theorem Measured.savedFrom {s t : ArmState} {base : BitVec 64} {desc : Desc} {value : Value}
    (measurement : Measured s t base desc value) : SavedFrom s t := by
  refine ⟨?_, ?_, ?_, measurement.vectors⟩
  · change r (.GPR 31#5) t + 144#64 = r (.GPR 31#5) s
    rw [measurement.registers.stack]
    simp [SszArm.Serialize.Args.bodySP, SszArm.Serialize.Args.ofEntry,
      BitVec.sub_eq_add_neg, BitVec.add_assoc]
  · intro reg displacement member
    change read_mem_bytes 8 (r (.GPR 31#5) t + BitVec.ofNat 64 displacement) t = _
    rw [measurement.registers.stack]
    exact measurement.saved reg displacement member
  · intro reg lower upper outside
    have notLR : reg ≠ 30#5 := by
      intro same
      subst reg
      exact outside (by simp)
    have below : reg.toNat ≤ 29 := by bv_omega
    apply measurement.untouched reg lower below
    intro member
    apply outside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with h | h | h | h | h <;> simp [h]

 theorem Measured.measureSpace {s t : ArmState} {base : BitVec 64} {desc : Desc} {value : Value}
    (measurement : Measured s t base desc value) (owned : Owned s (Args.ofEntry s) desc value) :
    SszArm.Serialize.Finish.MeasureSpace t := by
  have minimum := requiredStack_min desc
  have enough := owned.stackLow
  have stackAddress := SszArm.Serialize.bodySP_toNat (Args.ofEntry s) (by omega)
  have originalHigh := (Args.ofEntry s).stack.isLt
  have separate := (owned.resultStack.resolve_left (by decide))
    ((Args.ofEntry s).stack.toNat - requiredStack desc, requiredStack desc)
    (by simp [stackSpans, Stack.envelope])
  constructor
  · change (r (.GPR 31#5) t).toNat + 144 ≤ 2^64
    rw [measurement.registers.stack, stackAddress]
    omega
  · change (r (.GPR 19#5) t).toNat + 72 ≤ 2^64
    rw [measurement.registers.result]
    exact owned.result.2.2.1
  · change (r (.GPR 19#5) t).toNat + 72 ≤ (r (.GPR 31#5) t).toNat + 8 ∨
      (r (.GPR 31#5) t).toNat + 144 ≤ (r (.GPR 19#5) t).toNat
    rw [measurement.registers.result, measurement.registers.stack, stackAddress]
    dsimp at separate
    omega

 theorem Measured.error_saved_protected {s t : ArmState} {base : BitVec 64}
    {desc : Desc} {value : Value} (measurement : Measured s t base desc value)
    (owned : Owned s (Args.ofEntry s) desc value) :
    Protected (SszArm.Serialize.Finish.measureWrites t)
      ((SszArm.Serialize.Finish.sp t).toNat + 96) 48 := by
  have space := measurement.measureSpace owned
  right
  intro span member
  simp only [SszArm.Serialize.Finish.measureWrites, List.mem_cons, List.mem_singleton] at member
  rcases member with rfl | rfl
  · right
    dsimp
    omega
  · have separate := space.separate
    dsimp
    omega

/-- The recursive helper restores the wrapper's working registers; the actual
error-copy epilogue restores the caller's original AAPCS state from saved slots. -/
theorem Measured.error_returned {s m : ArmState} {base : BitVec 64}
    {desc : Desc} {value : Value} (measurement : Measured s m base desc value)
    (owned : Owned s (Args.ofEntry s) desc value) :
    Delimited.Returned s (SszArm.Serialize.Finish.measureReturned base m) := by
  have space := measurement.measureSpace owned
  have copiedFrame := SszArm.Serialize.Finish.measure_copy_frame base m space
  have saved : SavedFrom s
      (SszArm.Serialize.Finish.measureCopied base m) := by
    apply measurement.savedFrom.of_frame copiedFrame
      (SszArm.Serialize.Finish.measure_copied_sp base m) space.stackHigh
      (measurement.error_saved_protected owned)
    · intro reg lower upper outside
      apply SszArm.Serialize.Finish.measure_copied_register
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      repeat' constructor
      all_goals intro same; bv_omega
    · intro reg lower upper
      rw [SszArm.Serialize.Finish.measure_copied_vector]
  exact returned_original s (SszArm.Serialize.Finish.measureCopied base m) saved
    ((SszArm.Serialize.Finish.measure_copied_error base m).trans measurement.error)

end SszArm.Codec.Serialize
