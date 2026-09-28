import SszArm.NatMulWordIdentityOwned
import SszArm.NatMulWordReturnValues
import SszArm.NatAddZeroOwned

namespace SszArm.NatMulWord

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

@[simp] theorem identity_outcome (s : ArmState) (operand : SszNative.NatOperand) :
    outcome s operand 1#64 =
      SszNative.NatArithmetic.unchanged (arenaOf s).used (.ok operand.normalized) := by
  simp [outcome, SszNative.NatMul.runWord]

theorem identity_writes (s : ArmState) (operand : SszNative.NatOperand) :
    writesFor s (outcome s operand 1#64) =
      [((r (.GPR 31#5) s).toNat - 48, 48), ((r (.GPR 0#5) s).toNat, 16),
       ((r (.GPR 0#5) s).toNat + 64, 4)] := by
  simp [writesFor, localWrites, SszNative.NatArithmetic.unchanged]

theorem identity_values_protected (s : ArmState) (operand : SszNative.NatOperand)
    (address bytes : Nat) (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (owned : Protected (writesFor s (outcome s operand 1#64)) address bytes) :
    Protected (valueWrites s) address bytes := by
  rcases owned with empty | separate
  · exact Or.inl empty
  · right
    have work := separate ((r (.GPR 31#5) s).toNat - 48, 48) (by rw [identity_writes]; simp)
    have output := separate ((r (.GPR 0#5) s).toNat, 16) (by rw [identity_writes]; simp)
    have status := separate ((r (.GPR 0#5) s).toNat + 64, 4) (by rw [identity_writes]; simp)
    intro span member
    simp only [valueWrites, NatAdd.valueWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp only [Prod.fst, Prod.snd] at * <;> omega

theorem Owned.identity_values {s : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned s operand 1#64) : NatAdd.OperandOwned (valueWrites s) operand := by
  cases operand with
  | small word => trivial
  | large pointer words =>
    exact identity_values_protected s (.large pointer words) pointer.toNat (8 * words.length)
      owned.stackBound owned.inputOwned

theorem ScanFrame.value_writes {s t : ArmState} (frame : ScanFrame s t) :
    valueWrites t = valueWrites s := by
  simp only [valueWrites, NatAdd.valueWrites, frame.sp, frame.registers 0#5 (by decide)]

theorem ScanFrame.values {s t : ArmState} (frame : ScanFrame s t)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) : MemoryFrame (valueWrites s) s t := by
  intro a outside
  apply frame.memory
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [valueWrites, NatAdd.valueWrites])
  simp only [Prod.fst, Prod.snd] at work
  omega

theorem ScanFrame.return_owned {s t : ArmState} (frame : ScanFrame s t)
    (owned : ReturnOwned s) : ReturnOwned t := by
  have out := frame.registers 0#5 (by decide)
  exact ⟨by simpa only [frame.sp] using owned.stack,
    by simpa only [out] using owned.output,
    by simpa only [out, frame.sp] using owned.separate⟩

theorem ScanFrame.returned {s t u : ArmState} (frame : ScanFrame s t)
    (returned : Returned t u) : Returned s u := by
  refine ⟨returned.pc.trans (frame.registers _ (by decide)), returned.error,
    returned.sp.trans frame.sp, ?_, ?_⟩
  · intro reg lo hi
    apply (returned.registers reg lo hi).trans
    apply frame.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · bv_omega
    constructor
    · bv_omega
    constructor
    · bv_omega
    constructor
    · bv_omega
    constructor
    · bv_omega
    constructor <;> bv_omega
  · intro reg lo hi
    exact (returned.vectors reg lo hi).trans
      (congrArg (fun x : BitVec 128 => x.setWidth 64) (frame.vectors reg))

theorem identity_frame {s t : ArmState} (operand : SszNative.NatOperand)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) (frame : MemoryFrame (valueWrites s) s t) :
    MemoryFrame (writesFor s (outcome s operand 1#64)) s t := by
  intro a outside
  apply frame a
  have work := outside ((r (.GPR 31#5) s).toNat - 48, 48) (by rw [identity_writes]; simp)
  have output := outside ((r (.GPR 0#5) s).toNat, 16) (by rw [identity_writes]; simp)
  have status := outside ((r (.GPR 0#5) s).toNat + 64, 4) (by rw [identity_writes]; simp)
  intro span member
  simp only [valueWrites, NatAdd.valueWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp only [Prod.fst, Prod.snd] at * <;> omega

/-- A no-allocation identity return leaves all arena fields and every raw input
byte unchanged, including high zero limbs omitted from the returned slice. -/
theorem identity_post_of_frame (s t : ArmState) (operand : SszNative.NatOperand)
    (owned : Owned s operand 1#64) (returned : Returned s t)
    (result : SszNative.NatArithmetic.AddResultAt (widthLoad t)
      (r (.GPR 0#5) s).toNat (.ok operand.normalized))
    (frame : MemoryFrame (valueWrites s) s t) : Post s t operand 1#64 := by
  have full := identity_frame operand owned.stackBound frame
  have arena : Protected (writesFor s (outcome s operand 1#64))
      (r (.GPR 4#5) s).toNat 24 := by
    simpa only [writesFor, identity_outcome, SszNative.NatArithmetic.unchanged] using owned.arenaLocal
  have physical := owned.arenaBound
  have capAddress : (r (.GPR 4#5) s + 8#64).toNat = (r (.GPR 4#5) s).toNat + 8 := by bv_omega
  have usedAddress : (r (.GPR 4#5) s + 16#64).toNat = (r (.GPR 4#5) s).toNat + 16 := by bv_omega
  have baseSame := full.read (r (.GPR 4#5) s) 8 (by omega)
    (by simpa using arena.subspan 0 8 (by decide))
  have capSame := full.read (r (.GPR 4#5) s + 8#64) 8 (by rw [capAddress]; omega)
    (by rw [capAddress]; exact arena.subspan 8 8 (by decide))
  have usedSame := full.read (r (.GPR 4#5) s + 16#64) 8 (by rw [usedAddress]; omega)
    (by rw [usedAddress]; exact arena.subspan 16 8 (by decide))
  refine ⟨returned, ?_, ?_, ?_, full,
    NatAdd.operand_preserved full operand owned.operandAt owned.inputOwned, baseSame, capSame⟩
  · simpa only [identity_outcome, SszNative.NatArithmetic.unchanged] using result
  · intro reservation allocated
    simp [SszNative.NatArithmetic.unchanged] at allocated
  · simp only [identity_outcome, SszNative.NatArithmetic.unchanged, arenaOf, usedSame]

end SszArm.NatMulWord
