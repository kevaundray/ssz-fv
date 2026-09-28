import SszArm.MeasureOwnership

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)
open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- Allocation-free leaves derive their complete arena post from the byte frame,
without requiring a future cursor or header observation. -/
theorem Produced.of_no_calls {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    {base : BitVec 64} (owned : Owned s args desc value)
    (noCalls : (outcome s args desc value).calls = [])
    (used : (outcome s args desc value).used = (arenaOf s args).used)
    (pc : read_pc t = base + 4116#64) (program : t.program = s.program)
    (error : read_err t = .None) (stack : r (.GPR 31#5) t = args.bodySP)
    (result : ResultAt (widthLoad t) args.result.toNat (outcome s args desc value).result)
    (frame : MemoryFrame (bodyWrites args (outcome s args desc value)) s t)
    (registers : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5, 29#5] →
      r (.GPR reg) t = r (.GPR reg) s)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64) :
    Produced s t args desc value base := by
  have localFrame : MemoryFrame (localWrites args (outcome s args desc value)) s t := by
    apply frame.weaken
    intro span member
    simp [bodyWrites, allocationWrites, noCalls] at member
    rcases member with stackMember | resultMember
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr stackMember)))
    · exact List.mem_append.mpr (Or.inr resultMember)
  have r0 := Emit.frame_read_offset localFrame args.arena 24 0 8 owned.arenaBound
    owned.headerLocal (by decide)
  have r8 := Emit.frame_read_offset localFrame args.arena 24 8 8 owned.arenaBound
    owned.headerLocal (by decide)
  have r16 := Emit.frame_read_offset localFrame args.arena 24 16 8 owned.arenaBound
    owned.headerLocal (by decide)
  simp only [BitVec.add_zero] at r0
  refine ⟨pc, program, error, stack, result, ?_, ⟨r0, r8⟩, ?_, frame, registers, vectors⟩
  · rw [r16, used]
    rfl
  · intro call member
    simp only [noCalls, List.not_mem_nil] at member

/-- Original live fields, every padded limb, and backing storage follow from the
precise write frame. Neither output initialization nor successful sizing is used. -/
theorem post_of_return (s t : ArmState) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value)
    (returned : Returned s t)
    (result : ResultAt (widthLoad t) (Args.ofEntry s).result.toNat
      (outcome s (Args.ofEntry s) desc value).result)
    (cursor : (read_mem_bytes 8 ((Args.ofEntry s).arena + 16#64) t).toNat =
      (outcome s (Args.ofEntry s) desc value).used)
    (header : read_mem_bytes 8 (Args.ofEntry s).arena t = read_mem_bytes 8 (Args.ofEntry s).arena s ∧
      read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) t =
        read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) s)
    (written : ∀ call ∈ (outcome s (Args.ofEntry s) desc value).calls,
      NatDivision.WrittenAt (widthLoad t) call)
    (frame : MemoryFrame (writesFor (Args.ofEntry s) (outcome s (Args.ofEntry s) desc value)) s t) :
    Post s t desc value := by
  refine ⟨returned, result, cursor, header, written, frame,
    descriptor_preserved owned frame, value_preserved owned frame, ?_, ?_⟩
  · intro operand member
    exact NatDivision.operand_preserved frame operand (owned.operand_at operand member)
      (owned.operandOwned operand member)
  · intro span member address low high
    exact frame.protected_byte (owned.backingOwned span member) address low high

/-- Wrapper callers obtain the returned size's complete Nat representation. -/
theorem Post.success_operand {s t : ArmState} {desc : Desc} {value : Value}
    (post : Post s t desc value) (operand : NatOperand)
    (success : (outcome s (Args.ofEntry s) desc value).result = .ok operand) :
    SszNative.NatArithmetic.operandAt (widthLoad t) ((Args.ofEntry s).result.toNat + 16) operand := by
  have result := post.result
  simp only [success, ResultAt] at result
  exact result.2.2.1

/-- Scope/Limit retain ownership of both payload Nat observations, including any
committed actual-count allocation and the original padded descriptor operand. -/
theorem Post.error_operands {s t : ArmState} {desc : Desc} {value : Value}
    (post : Post s t desc value) (reason : SszNative.Serialize.Error)
    (failure : (outcome s (Args.ofEntry s) desc value).result = .error reason) :
    SszNative.NatArithmetic.operandAt (widthLoad t) ((Args.ofEntry s).result.toNat + 16)
        (errorOperands reason).1 ∧
      SszNative.NatArithmetic.operandAt (widthLoad t) ((Args.ofEntry s).result.toNat + 32)
        (errorOperands reason).2 := by
  have result := post.result
  simp only [failure, ResultAt, ErrorAt] at result
  exact ⟨result.2.2.1, result.2.2.2.1⟩

/-- The accepted pure refinement gives SSZ semantic correspondence without
turning scratch exhaustion into a precondition. -/
theorem Post.refines {s t : ArmState} {desc : Desc} {value : Value}
    (post : Post s t desc value) (physical : value.Physical) :
    ∃ result, ResultAt (widthLoad t) (Args.ofEntry s).result.toNat result ∧
      SszNative.Serialize.Measures result (SszNative.Serialize.expectedSize desc value) :=
  ⟨(outcome s (Args.ofEntry s) desc value).result, post.result,
    SszNative.Serialize.measure_refines desc value (arenaOf s (Args.ofEntry s)) physical⟩

end SszArm.Measure
