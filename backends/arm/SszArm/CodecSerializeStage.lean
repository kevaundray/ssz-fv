import SszArm.SerializeFinishStage
import SszCodecMeasure

namespace SszArm.Codec.Serialize

open Delimited (Protected MemoryFrame)
open UintCodec (widthLoad)
open SszNative.CodecMeasure (Plan PlanFields)

/-- Transport the five active fields independently of Result padding and the
recursive children they name. The latter are transported by storage framing. -/
theorem planFields_frame {s t : ArmState} {writes : List Delimited.Span}
    {address : Nat} {plan : Plan} (frame : MemoryFrame writes s t)
    (bound : address + 40 ≤ 2^64) (owned : Protected writes address 40)
    (fields : PlanFields (widthLoad s) address plan) :
    PlanFields (widthLoad t) address plan := by
  have same (offset : Nat) (within : offset + 8 ≤ 40) :
      widthLoad t (address + offset) 8 = widthLoad s (address + offset) 8 :=
    frame.load _ _ (by omega) (owned.subspan offset 8 within)
  rcases fields with ⟨children, count, pointer, payload, leading⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using (same 0 (by decide)).trans children
  · exact (same 8 (by decide)).trans count
  · exact (same 16 (by decide)).trans pointer
  · exact (same 24 (by decide)).trans payload
  · exact (same 32 (by decide)).trans leading

private theorem word_of_observe (s : ArmState) (address : BitVec 64)
    (offset : Nat) (word : BitVec 64)
    (observed : widthLoad s (address.toNat + offset) 8 = some word.toNat) :
    read_mem_bytes 8 (address + BitVec.ofNat 64 offset) s = word := by
  apply BitVec.eq_of_toNat_eq
  simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Option.some.injEq] using observed

/-- The recursive Plan's Nat size is loaded unchanged. In particular a borrowed
large, empty, or high-zero-padded Nat is not narrowed at this stage. -/
theorem success_stage_size (base : BitVec 64) (s : ArmState) (plan : Plan)
    (fields : PlanFields (widthLoad s) ((SszArm.Serialize.Finish.sp s).toNat + 24) plan) :
    r (.GPR 8#5) (SszArm.Serialize.Finish.successStage base s) = plan.size.pointer ∧
      r (.GPR 5#5) (SszArm.Serialize.Finish.successStage base s) = plan.size.payload := by
  have loaded := SszArm.Serialize.Finish.success_stage_fields base s
  constructor
  · apply loaded.1.trans
    apply word_of_observe s (SszArm.Serialize.Finish.sp s) 40 plan.size.pointer
    simpa only [Nat.add_assoc] using fields.2.2.1
  · apply loaded.2.1.trans
    apply word_of_observe s (SszArm.Serialize.Finish.sp s) 48 plan.size.payload
    simpa only [Nat.add_assoc] using fields.2.2.2.1

/-- Actual PC52..148 staging with a recursive Plan. No claim is made about the
unused Result tail; the emitted child-plan pointer and leading word are retained. -/
theorem success_stage_correct (base : BitVec 64) (s : ArmState) (plan : Plan)
    (code : SszArm.Serialize.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 52#64)
    (physical : (SszArm.Serialize.Finish.sp s).toNat + 96 ≤ 2^64)
    (status : read_mem_bytes 4 (SszArm.Serialize.Finish.sp s + 88#64) s = 0#32)
    (fields : PlanFields (widthLoad s) ((SszArm.Serialize.Finish.sp s).toNat + 24) plan) :
    run 10 s = SszArm.Serialize.Finish.successStage base s ∧
      read_pc (SszArm.Serialize.Finish.successStage base s) = base + 152#64 ∧
      PlanFields (widthLoad (SszArm.Serialize.Finish.successStage base s))
        ((SszArm.Serialize.Finish.sp s).toNat + 24) plan ∧
      MemoryFrame [((SszArm.Serialize.Finish.sp s).toNat + 8, 16)]
        s (SszArm.Serialize.Finish.successStage base s) := by
  have frame := SszArm.Serialize.Finish.success_stage_frame base s (by omega)
  refine ⟨SszArm.Serialize.Finish.success_stage_run base s code error aligned pc status,
    SszArm.Serialize.Finish.success_stage_pc base s status, ?_, frame⟩
  apply planFields_frame frame (by omega) _ fields
  right
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  right
  dsimp
  omega

end SszArm.Codec.Serialize
