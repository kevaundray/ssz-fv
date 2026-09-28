import SszArm.EmitScalarOps
import SszArm.EmitMemory
import SszArm.Udivti3Arithmetic

namespace SszArm.Emit.Scalar

open SszNative.Serialize (Desc)

def ByteKind (desc : Desc) : Prop :=
  ∃ operand, desc = .byteVector operand ∨ desc = .byteList operand

theorem bytes_size {s : ArmState} {args : Args} {desc : Desc} {bytes : Ssz.Bytes} {size : Nat}
    (kind : ByteKind desc) (owned : Owned s args desc (.bytes bytes) size) : size = bytes.size := by
  rcases kind with ⟨operand, rfl | rfl⟩ <;>
    have expected := owned.expected
  all_goals
    simp only [SszNative.Serialize.expectedSize] at expected
    split at expected <;> simp_all

theorem bytes_emit (desc : Desc) (bytes : Ssz.Bytes) (kind : ByteKind desc) :
    SszNative.Serialize.emit desc (.bytes bytes) = bytes := by
  rcases kind with ⟨operand, rfl | rfl⟩ <;> rfl

def bytesOps : List Op := [.p820, .p824, .p828, .p832, .p836, .p840, .p844, .p848, .p852]

@[irreducible] def bytesSetup (s : ArmState) : ArmState := block bytesOps s

theorem bytes_setup_memory (s : ArmState) : (bytesSetup s).mem = s.mem := by
  simp [bytesSetup, block, bytesOps, Op.effect, put, next, state_simp_rules]

theorem bytes_setup_program (s : ArmState) : (bytesSetup s).program = s.program := by
  simp [bytesSetup, block, bytesOps, Op.effect, put, next, state_simp_rules]

theorem bytes_setup_error (s : ArmState) : read_err (bytesSetup s) = read_err s := by
  simp [bytesSetup, block, bytesOps, Op.effect, put, next, state_simp_rules]

theorem bytes_setup_register (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [0#5, 1#5, 2#5, 8#5, 23#5]) :
    r (.GPR reg) (bytesSetup s) = r (.GPR reg) s := by
  have h0 : reg ≠ 0#5 := by simp_all
  have h1 : reg ≠ 1#5 := by simp_all
  have h2 : reg ≠ 2#5 := by simp_all
  have h8 : reg ≠ 8#5 := by simp_all
  have h23 : reg ≠ 23#5 := by simp_all
  simp [bytesSetup, block, bytesOps, Op.effect, put, next, state_simp_rules, h0, h1, h2, h8, h23]

theorem bytes_setup_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (bytesSetup s) = r (.SFP reg) s := by
  simp [bytesSetup, block, bytesOps, Op.effect, put, next, state_simp_rules]

theorem bytes_setup_arguments (s : ArmState) (args : Args) (registers : BodyRegisters s args) :
    r (.GPR 0#5) (bytesSetup s) = args.output ∧
    r (.GPR 1#5) (bytesSetup s) = read_mem_bytes 8 (args.value + 8#64) s ∧
    r (.GPR 2#5) (bytesSetup s) = read_mem_bytes 8 (args.value + 16#64) s ∧
    r (.GPR 23#5) (bytesSetup s) = read_mem_bytes 8 (args.value + 16#64) s := by
  simp (config := {decide := true}) [bytesSetup, block, bytesOps, Op.effect, put, next,
    state_simp_rules, registers.output, registers.value]

theorem bytes_setup_run (s : ArmState) (base : BitVec 64) (args : Args) (desc : Desc)
    (bytes : Ssz.Bytes) (size : Nat) (kind : ByteKind desc)
    (owned : Owned s args desc (.bytes bytes) size) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 820#64) (tag : r (.GPR 8#5) s = descriptorTag desc) :
    run 9 s = bytesSetup s ∧ read_pc (bytesSetup s) = base + 856#64 := by
  have masked : r (.GPR 8#5) s &&& 14#64 = 2#64 := by
    rw [tag]
    rcases kind with ⟨operand, rfl | rfl⟩ <;> simp only [descriptorTag] <;> decide
  have count := owned.value_at.2.1
  have fitting : (read_mem_bytes 8 (r (.GPR 22#5) s + 16#64) s).toNat ≤
      (r (.GPR 21#5) s).toNat := by
    rw [registers.value, registers.capacity, count, ← bytes_size kind owned]
    exact owned.fitting
  have guard : ¬ ((AddWithCarry (read_mem_bytes 8 (r (.GPR 22#5) s + 16#64) s)
      (~~~r (.GPR 21#5) s) 1#1).2.c = 1#1 ∧
      (AddWithCarry (read_mem_bytes 8 (r (.GPR 22#5) s + 16#64) s)
      (~~~r (.GPR 21#5) s) 1#1).2.z ≠ 1#1) := by
    intro rejected
    have zero : (AddWithCarry (read_mem_bytes 8 (r (.GPR 22#5) s + 16#64) s)
        (~~~r (.GPR 21#5) s) 1#1).2.z = 0#1 := by
      have := rejected.2
      bv_omega
    have high := (Udivti3.cmp_high _ _).mp ⟨rejected.1, zero⟩
    omega
  have follows : Follows base bytesOps s := by
    change r .PC s = _ at pc
    simp (config := {decide := true}) [bytesOps, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, pc, masked, guard, BitVec.add_assoc]
  refine ⟨?_, ?_⟩
  · have executed := runs bytesOps s base code error aligned follows
    change run 9 s = block bytesOps s at executed
    simpa only [bytesSetup] using executed
  · change r .PC s = _ at pc
    simp (config := {decide := true}) [bytesSetup, block, bytesOps, Op.effect, put, next,
      state_simp_rules, pc, masked, guard, BitVec.add_assoc]

end SszArm.Emit.Scalar
