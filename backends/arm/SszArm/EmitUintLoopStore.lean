import SszArm.EmitUintByteExec
import SszArm.EmitUintFrame
import SszArm.NatAddLoopMemory

namespace SszArm.Emit.Uint

open SszNative (NatOperand)
open UintCodec (widthLoad)
open Delimited (MemoryFrame Protected)

inductive ByteStoreKind where
  | small | large
  deriving DecidableEq

def ByteStoreKind.start : ByteStoreKind → Nat
  | .small => 964 | .large => 1096

def ByteStoreKind.index : ByteStoreKind → BitVec 5
  | .small => 10#5 | .large => 11#5

def ByteStoreKind.ops : ByteStoreKind → List ByteOp
  | .small => [.p964, .p968, .p972, .p976, .p980, .p984, .p988]
  | .large => [.p1096, .p1100, .p1104, .p1108, .p1112, .p1116, .p1120]

def byteStoreAddress (s : ArmState) (kind : ByteStoreKind) : BitVec 64 :=
  r (.GPR 20#5) s + r (.GPR kind.index) s

def byteStoreMemory (s : ArmState) (kind : ByteStoreKind) : ArmState :=
  write_mem_bytes 1 (byteStoreAddress s kind) ((r (.GPR 12#5) s).setWidth 8)
    (NatCompare.saved s 9#5)

@[irreducible] def byteStored (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (kind.start + 28)) (byteStoreMemory s kind)

private def byteStoreSequence (s : ArmState) (index : BitVec 5) : ArmState :=
  let s := put 31 (r (.GPR 31#5) s - 16#64) s
  let s := next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  let s := put 9 (r (.GPR index) s) s
  let s := put 9 (r (.GPR 20#5) s + r (.GPR 9#5) s) s
  let s := next (write_mem_bytes 1 (r (.GPR 9#5) s) ((r (.GPR 12#5) s).setWidth 8) s)
  let s := put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  put 31 (r (.GPR 31#5) s + 16#64) s

private theorem byteStoreSequence_eq (s : ArmState) (kind : ByteStoreKind)
    (restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (byteStoreMemory s kind) = r (.GPR 9#5) s) :
    byteStoreSequence s kind.index = w .PC (read_pc s + 28#64) (byteStoreMemory s kind) := by
  have restored := NatAdd.store_restore_fields (byteStoreMemory s kind) 9#5
    (byteStoreAddress s kind) (by decide)
  simp only [byteStoreMemory, NatCompare.saved, r_of_write_mem_bytes] at restore restored ⊢
  cases kind <;> simp only [byteStoreAddress, ByteStoreKind.index] at restore restored ⊢
  all_goals
    simpa (config := {decide := true})
      [byteStoreSequence, put, next, Dispatch.next,
       NatAdd.load_store_field, NatAdd.load_gpr_pc, state_simp_rules,
       BitVec.add_assoc, BitVec.sub_add_cancel, restore] using
      congrArg (w .PC (read_pc s + 28#64)) restored

private theorem byteStore_run_of_restore (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.start)
    (restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (byteStoreMemory s kind) = r (.GPR 9#5) s) :
    run 7 s = byteStored s base kind := by
  have position : r .PC s = base + BitVec.ofNat 64 kind.start := pc
  have follows : ByteFollows base kind.ops s := by
    cases kind <;> simp [ByteStoreKind.ops, ByteStoreKind.start, ByteFollows,
      ByteOp.row, ByteOp.effect, put, next, Dispatch.next, state_simp_rules, position, BitVec.add_assoc]
  rw [show 7 = kind.ops.length by cases kind <;> rfl, byte_run base kind.ops s code error aligned follows]
  have sequence : byteBlock base kind.ops s = byteStoreSequence s kind.index := by cases kind <;> rfl
  rw [sequence, byteStoreSequence_eq s kind restore, byteStored]
  simp only [pc, BitVec.ofNat_add, BitVec.add_assoc]

/-- The current output byte is physically inside the caller's live slice. -/
theorem byteStore_position {s : ArmState} {args : Args} {width number : NatOperand} {size index : Nat}
    (kind : ByteStoreKind) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (current : (r (.GPR kind.index) s).toNat = index)
    (inside : index < size) : (byteStoreAddress s kind).toNat = args.output.toNat + index := by
  have fitting := owned.fitting
  have bound := owned.outputBound
  simp only [byteStoreAddress, registers.output]
  bv_omega

theorem byte_store_run {s : ArmState} {args : Args} {width number : NatOperand} {size index : Nat}
    (base : BitVec 64) (kind : ByteStoreKind) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 kind.start)
    (current : (r (.GPR kind.index) s).toNat = index) (inside : index < size) :
    run 7 s = byteStored s base kind := by
  apply byteStore_run_of_restore s base kind code error aligned pc
  have position := byteStore_position kind owned registers current inside
  have stack := body_stack_safe owned registers
  have low := owned.stackLow
  have capacity := owned.fitting
  have bounded := owned.outputBound
  have slot : (r (.GPR 31#5) s - 16#64).toNat = args.stack.toNat - 176 := by
    rw [registers.stack]
    unfold Args.bodySP
    bv_omega
  have apart : Protected [((byteStoreAddress s kind).toNat, 1)]
      (r (.GPR 31#5) s - 16#64).toNat 8 := by
    right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    rcases owned.outputStack with empty | separate
    · omega
    · have separated := separate (args.stack.toNat - 176, 16) (by simp [stackWrites])
      simp only [Prod.fst, Prod.snd] at separated ⊢
      rw [slot, position]
      omega
  unfold byteStoreMemory
  rw [(Delimited.store_frame (NatCompare.saved s 9#5) (byteStoreAddress s kind) 1
    ((r (.GPR 12#5) s).setWidth 8) (by rw [position]; omega)).read _ 8 (by bv_omega) apart]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)

@[simp] theorem byteStored_program (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind) :
    (byteStored s base kind).program = s.program := by
  simp [byteStored, byteStoreMemory, NatCompare.saved, state_simp_rules]

@[simp] theorem byteStored_error (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind) :
    read_err (byteStored s base kind) = read_err s := by
  simp [byteStored, byteStoreMemory, NatCompare.saved, state_simp_rules]

@[simp] theorem byteStored_register (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind) (reg : BitVec 5) :
    r (.GPR reg) (byteStored s base kind) = r (.GPR reg) s := by
  simp [byteStored, byteStoreMemory, NatCompare.saved, state_simp_rules]

@[simp] theorem byteStored_flag (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind) (flag : PFlag) :
    r (.FLAG flag) (byteStored s base kind) = r (.FLAG flag) s := by
  simp [byteStored, byteStoreMemory, NatCompare.saved, state_simp_rules]

@[simp] theorem byteStored_vector (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind) (reg : BitVec 5) :
    r (.SFP reg) (byteStored s base kind) = r (.SFP reg) s := by
  simp [byteStored, byteStoreMemory, NatCompare.saved, state_simp_rules]

@[simp] theorem byteStored_pc (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind) :
    read_pc (byteStored s base kind) = base + BitVec.ofNat 64 (kind.start + 28) := by
  simp [byteStored, state_simp_rules]

end SszArm.Emit.Uint
