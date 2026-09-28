import SszArm.EmitScalarOps
import SszArm.EmitMemory
import SszArm.NatExactState

namespace SszArm.Emit.Scalar

open UintCodec (widthLoad)
open Delimited (MemoryFrame Protected)

def boolOps : List Op := [.p344, .p796, .p800, .p804, .p808, .p812, .p816]

@[irreducible] def boolResult (s : ArmState) (base : BitVec 64) (args : Args) (flag : Bool) : ArmState :=
  w .PC (base + 1004#64)
    (write_mem_bytes 1 args.output (if flag then 1#8 else 0#8)
      (write_mem_bytes 8 args.result 1#64
        (w (.GPR 9#5) 1#64 (w (.GPR 8#5) (if flag then 1#64 else 0#64) s))))

theorem bool_runs (s : ArmState) (base : BitVec 64) (args : Args) (flag : Bool) (size : Nat)
    (owned : Owned s args .bool (.bool flag) size) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 344#64) (tag : r (.GPR 9#5) s = 0#64) :
    run 7 s = boolResult s base args flag := by
  have sizeEq : size = 1 := by
    have expected := owned.expected
    simpa [SszNative.Serialize.expectedSize] using expected.symm
  have capacity : r (.GPR 21#5) s ≠ 0#64 := by
    have fitting := owned.fitting
    rw [registers.capacity]
    rw [sizeEq] at fitting
    bv_omega
  have payload := owned.value_at.2
  change read_mem_bytes 1 (args.value + 1#64) s = (if flag then 1#8 else 0#8) at payload
  have follows : Follows base boolOps s := by
    change r .PC s = _ at pc
    simp (config := {decide := true}) [boolOps, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, pc, tag, capacity, BitVec.add_assoc]
  have execution := runs boolOps s base code error aligned follows
  change run 7 s = _ at execution
  rw [execution]
  change r .PC s = _ at pc
  cases flag <;>
    simp (config := {decide := true}) [block, boolOps, Op.effect, put, next, boolResult,
      state_simp_rules, pc, tag, capacity, registers.value, registers.output,
      registers.result, payload, BitVec.add_assoc]
  all_goals simp only [NatExact.store_w, NatExact.gpr_w_pc, w_of_w_shadow]

theorem bool_produced (s : ArmState) (base : BitVec 64) (args : Args) (flag : Bool) (size : Nat)
    (owned : Owned s args .bool (.bool flag) size) (registers : BodyRegisters s args)
    (error : read_err s = .None) :
    Produced s (boolResult s base args flag) args .bool (.bool flag) size base := by
  have sizeEq : size = 1 := by
    have expected := owned.expected
    simpa [SszNative.Serialize.expectedSize] using expected.symm
  subst size
  have resultBound : args.result.toNat + 8 ≤ 2^64 := by have := owned.resultBound; omega
  have outputBound : args.output.toNat + 1 ≤ 2^64 := by
    have := owned.outputBound
    have := owned.fitting
    omega
  have apart : args.result.toNat + 8 ≤ args.output.toNat ∨
      args.output.toNat + 1 ≤ args.result.toNat := by
    rcases owned.outputResult with empty | separated
    · have := owned.fitting; omega
    · have h := separated (args.result.toNat, 8) (by simp)
      have := owned.fitting
      change args.output.toNat + args.capacity.toNat ≤ args.result.toNat ∨
        args.result.toNat + 8 ≤ args.output.toNat at h
      omega
  constructor
  · simp [boolResult, state_simp_rules]
  · simp [boolResult, state_simp_rules]
  · simpa [boolResult, state_simp_rules] using error
  · simpa (config := {decide := true}) [boolResult, state_simp_rules] using registers.result
  · simpa (config := {decide := true}) [boolResult, state_simp_rules] using registers.stack
  · simp only [boolResult, state_simp_rules]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 1 _ _ _ resultBound outputBound apart,
      BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ resultBound]
  · intro index within
    have zero : index = 0 := by
      simpa [SszNative.Serialize.emit] using within
    subst index
    cases flag <;>
      simp [SszNative.Serialize.emit, widthLoad, boolResult, state_simp_rules,
        BoolCodec.read_mem_bytes_write_mem_bytes_same, outputBound]
  · intro address outside
    have out := outside (args.output.toNat, 1) (by simp [bodyWrites])
    have result := outside (args.result.toNat, 8) (by simp [bodyWrites])
    simp only [boolResult, state_simp_rules]
    rw [BoolCodec.write_mem_bytes_frame _ _ 1 _ address outputBound out,
      BoolCodec.write_mem_bytes_frame _ _ 8 _ address resultBound result]
    simp only [state_simp_rules]
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp (config := {decide := true}) [boolResult, state_simp_rules]
  · intro reg low high
    simp [boolResult, state_simp_rules]

end SszArm.Emit.Scalar

namespace SszArm.Emit

theorem bool_body (s : ArmState) (base : BitVec 64) (args : Args) (flag : Bool) (size : Nat)
    (owned : Owned s args .bool (.bool flag) size) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 344#64) (tag : r (.GPR 9#5) s = 0#64) :
    ∃ steps t, run steps s = t ∧ Produced s t args .bool (.bool flag) size base :=
  ⟨7, Scalar.boolResult s base args flag,
    Scalar.bool_runs s base args flag size owned registers code error aligned pc tag,
    Scalar.bool_produced s base args flag size owned registers error⟩

end SszArm.Emit
