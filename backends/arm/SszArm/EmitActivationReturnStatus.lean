import SszArm.EmitActivationReturnOps

namespace SszArm.Emit

open ReturnBlock
open Activation (next put)
open Delimited (Span Protected MemoryFrame)

def statusOps : List ReturnBlock.Op :=
  [.p1004, .p1008, .p1012, .p1016, .p1020, .p1024, .p1028, .p1032, .p1036, .p1040]

@[irreducible] def statusStored (s : ArmState) : ArmState := ReturnBlock.block statusOps s

def statusMemory (s : ArmState) : ArmState :=
  write_mem_bytes 4 (r (.GPR 19#5) s + 64#64) 0#32
    (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (r (.GPR 10#5) s)
      (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s))

def statusWrites (args : Args) : List Span :=
  [(args.stack.toNat - 176, 16), (args.result.toNat + 64, 4)]

@[simp] theorem statusStored_program (s : ArmState) : (statusStored s).program = s.program := by
  simp [statusStored, statusOps, ReturnBlock.block]

@[simp] theorem statusStored_error (s : ArmState) : read_err (statusStored s) = read_err s := by
  simp [statusStored, statusOps, ReturnBlock.block]

@[simp] theorem statusStored_pc (s : ArmState) : read_pc (statusStored s) = read_pc s + 40#64 := by
  simp [statusStored, statusOps, ReturnBlock.block, ReturnBlock.Op.effect, next, put,
    state_simp_rules, BitVec.add_assoc]

@[simp] theorem statusStored_sp (s : ArmState) :
    r (.GPR 31#5) (statusStored s) = r (.GPR 31#5) s := by
  simp [statusStored, statusOps, ReturnBlock.block, ReturnBlock.Op.effect, next, put,
    state_simp_rules, BitVec.sub_add_cancel]

@[simp] theorem statusStored_register (s : ArmState) (reg : BitVec 5)
    (not9 : reg ≠ 9#5) (not10 : reg ≠ 10#5) (notSP : reg ≠ 31#5) :
    r (.GPR reg) (statusStored s) = r (.GPR reg) s := by
  simp [statusStored, statusOps, ReturnBlock.block, ReturnBlock.Op.effect, next, put,
    state_simp_rules, not9, not10, notSP]

@[simp] theorem statusStored_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (statusStored s) = r (.SFP reg) s := by
  simp [statusStored, statusOps, ReturnBlock.block, ReturnBlock.Op.effect, next, put, state_simp_rules]

@[simp] theorem statusStored_memory (s : ArmState) : (statusStored s).mem = (statusMemory s).mem := by
  simp [statusStored, statusOps, ReturnBlock.block, ReturnBlock.Op.effect, next, put,
    statusMemory, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem statusStored_aligned (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (statusStored s) := by
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, statusStored_sp] using aligned

theorem statusStored_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1004#64) : run 10 s = statusStored s := by
  have lower : Aligned (r (.GPR 31#5) s - 16#64) 4 := by
    simp (config := {decide := true}) [CheckSPAlignment, read_gpr,
      Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
    bv_omega
  rw [statusStored]
  apply ReturnBlock.runs statusOps s base code error
  change r .PC s = base + 1004#64 at pc
  simp (config := {decide := true}) [Follows, statusOps, ReturnBlock.Op.row,
    ReturnBlock.Op.effect, put, next, state_simp_rules, CheckSPAlignment, read_gpr,
    BitVec.setWidth_eq, pc, BitVec.add_assoc] at aligned lower ⊢
  exact ⟨aligned, lower⟩

theorem statusStored_frame {s : ArmState} {args : Args}
    (stack : r (.GPR 31#5) s = args.bodySP) (result : r (.GPR 19#5) s = args.result)
    (low : 176 ≤ args.stack.toNat) (bound : args.result.toNat + 68 ≤ 2^64) :
    MemoryFrame (statusWrites args) s (statusStored s) := by
  intro address outside
  have scratch := outside (args.stack.toNat - 176, 16) (by simp [statusWrites])
  have status := outside (args.result.toNat + 64, 4) (by simp [statusWrites])
  simp only [Prod.fst, Prod.snd] at scratch status
  rw [statusStored_memory]
  simp only [statusMemory, stack, result]
  rw [BoolCodec.write_mem_bytes_frame _ _ 4 _ address (by bv_omega) (by bv_omega)]
  rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address
    (by simp only [Args.bodySP]; bv_omega) (by simp only [Args.bodySP]; bv_omega)]
  exact BoolCodec.write_mem_bytes_frame _ _ 8 _ address
    (by simp only [Args.bodySP]; bv_omega) (by simp only [Args.bodySP]; bv_omega)

theorem statusStored_status (s : ArmState) (bound : (r (.GPR 19#5) s).toNat + 68 ≤ 2^64) :
    read_mem_bytes 4 (r (.GPR 19#5) s + 64#64) (statusStored s) = 0#32 := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (statusStored_memory s))]
  simp only [statusMemory]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 4 _ _ (by bv_omega)

theorem statusWrites_subset (args : Args) (size : Nat) (span : Span)
    (member : span ∈ statusWrites args) : span ∈ writesFor args size := by
  simp only [statusWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [writesFor, stackWrites]

end SszArm.Emit
