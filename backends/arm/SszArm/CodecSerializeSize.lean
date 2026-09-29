import SszArm.CodecSerializeStage
import SszArm.SerializeSize

namespace SszArm.Codec.Serialize

open Delimited (MemoryFrame)
open UintCodec (widthLoad)
open SszNative.CodecMeasure (Plan PlanFields)

/-- From the actual measurement return, restage the complete recursive Plan and
execute the native arbitrary-representation Nat narrowing loop and capacity
guard. Neither representability nor output capacity is assumed. -/
theorem after_measure_size_correct (base : BitVec 64) (s : ArmState) (plan : Plan)
    (capacity : BitVec 64)
    (code : SszArm.Serialize.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 52#64)
    (physical : (SszArm.Serialize.Finish.sp s).toNat + 96 ≤ 2^64)
    (stack : 16 ≤ (SszArm.Serialize.Finish.sp s).toNat)
    (status : read_mem_bytes 4 (SszArm.Serialize.Finish.sp s + 88#64) s = 0#32)
    (fields : PlanFields (widthLoad s) ((SszArm.Serialize.Finish.sp s).toNat + 24) plan)
    (input : plan.size.At (widthLoad s))
    (stageOwned : NatDivision.OperandOwned
      [((SszArm.Serialize.Finish.sp s).toNat + 8, 16)] plan.size)
    (sizeOwned : NatDivision.OperandOwned
      [((SszArm.Serialize.Finish.sp s).toNat - 16, 16)] plan.size)
    (cap : r (.GPR 23#5) s = capacity) :
    ∃ fuel t, run fuel s = t ∧
      SszArm.Serialize.Size.Post (SszArm.Serialize.Finish.successStage base s)
        t base plan.size capacity ∧
      PlanFields (widthLoad t) ((SszArm.Serialize.Finish.sp s).toNat + 24) plan ∧
      MemoryFrame ([((SszArm.Serialize.Finish.sp s).toNat + 8, 16)] ++
        SszArm.Serialize.Size.actualWrites (SszArm.Serialize.Finish.successStage base s) plan.size)
        s t := by
  let u := SszArm.Serialize.Finish.successStage base s
  obtain ⟨stageRun, stagePC, stageFields, stageFrame⟩ :=
    success_stage_correct base s plan code error aligned pc physical status fields
  have sizeRegisters := success_stage_size base s plan fields
  have sameSP : r (.GPR 31#5) u = r (.GPR 31#5) s :=
    SszArm.Serialize.Finish.success_stage_register base s 31#5 (by decide)
  have nextInput : plan.size.At (widthLoad u) :=
    NatDivision.operand_at_preserved stageFrame _ input stageOwned
  have nextOwned : NatDivision.OperandOwned
      [((r (.GPR 31#5) u).toNat - 16, 16)] plan.size := by
    simpa only [sameSP, SszArm.Serialize.Finish.sp] using sizeOwned
  have nextStack : 16 ≤ (r (.GPR 31#5) u).toNat := by
    simpa only [sameSP, SszArm.Serialize.Finish.sp] using stack
  have nextAligned : CheckSPAlignment u :=
    CheckSPAlignment_of_r_sp_aligned sameSP (BoolCodec.stack_aligned s aligned)
  obtain ⟨fuel, t, executed, post⟩ := SszArm.Serialize.Size.program_correct u base plan.size capacity
    (code.congr (SszArm.Serialize.Finish.success_stage_program base s))
    ((SszArm.Serialize.Finish.success_stage_error base s).trans error)
    nextAligned stagePC sizeRegisters.1 sizeRegisters.2
    ((SszArm.Serialize.Finish.success_stage_register base s 23#5 (by decide)).trans cap)
    nextInput nextOwned nextStack
  refine ⟨10 + fuel, t, ?_, post, ?_, ?_⟩
  · rw [run_plus, stageRun]
    exact executed
  · apply planFields_frame post.frame.memory (by omega) _ stageFields
    right
    intro span member
    simp only [SszArm.Serialize.Size.writes, List.mem_singleton] at member
    subst span
    right
    dsimp
    simp only [sameSP]
    change (r (.GPR 31#5) s).toNat - 16 + 8 ≤ (r (.GPR 31#5) s).toNat + 24
    omega
  · exact (stageFrame.weaken (fun _ member => List.mem_append.mpr (Or.inl member))).trans
      (post.footprint.weaken (fun _ member => List.mem_append.mpr (Or.inr member)))

end SszArm.Codec.Serialize
