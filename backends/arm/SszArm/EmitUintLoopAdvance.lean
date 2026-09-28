import SszArm.EmitUintLoopStoreMemory

namespace SszArm.Emit.Uint

open SszNative (NatOperand)

def ByteStoreKind.advanceStart : ByteStoreKind → Nat
  | .small => 992 | .large => 1124

def ByteStoreKind.loopStart : ByteStoreKind → Nat
  | .small => 936 | .large => 1132

def ByteStoreKind.nextIndex : ByteStoreKind → BitVec 5
  | .small => 11#5 | .large => 13#5

def ByteStoreKind.advanceOps : ByteStoreKind → List ByteOp
  | .small => [.p992, .p996] | .large => [.p1124, .p1128]

@[irreducible] def advanced (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind) : ArmState :=
  w .PC (if r (.FLAG .Z) s = 1#1 then base + 1000#64 else base + BitVec.ofNat 64 kind.loopStart)
    (w (.GPR kind.index) (r (.GPR kind.nextIndex) s) s)

theorem advance_run (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.advanceStart) :
    run 2 s = advanced s base kind := by
  have position : r .PC s = base + BitVec.ofNat 64 kind.advanceStart := pc
  have follows : ByteFollows base kind.advanceOps s := by
    cases kind <;> simp [ByteStoreKind.advanceOps, ByteStoreKind.advanceStart, ByteFollows,
      ByteOp.row, ByteOp.effect, put, next, Dispatch.next, state_simp_rules, position, BitVec.add_assoc]
  rw [show 2 = kind.advanceOps.length by cases kind <;> rfl,
    byte_run base kind.advanceOps s code error aligned follows]
  cases kind <;> simp [byteBlock, ByteStoreKind.advanceOps, advanced, ByteOp.effect,
    ByteStoreKind.index, ByteStoreKind.nextIndex, ByteStoreKind.loopStart,
    put, next, Dispatch.next, state_simp_rules, NatAdd.load_gpr_pc, w_of_w_shadow]

@[simp] theorem advanced_memory (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind) :
    (advanced s base kind).mem = s.mem := by simp [advanced, state_simp_rules]

@[simp] theorem advanced_index (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind) :
    r (.GPR kind.index) (advanced s base kind) = r (.GPR kind.nextIndex) s := by
  simp [advanced, state_simp_rules]

@[simp] theorem advanced_register (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind)
    (reg : BitVec 5) (different : reg ≠ kind.index) :
    r (.GPR reg) (advanced s base kind) = r (.GPR reg) s := by simp [advanced, state_simp_rules, different]

theorem advanced_frame (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind) (args : Args) (size : Nat) :
    Frame s (advanced s base kind) args size := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [advanced, state_simp_rules]
  · simp [advanced, state_simp_rules]
  · intro reg outside
    apply advanced_register
    cases kind <;> simp_all [ByteStoreKind.index]
  · intro reg
    simp [advanced, state_simp_rules]
  · intro address outside
    rw [advanced_memory]

theorem advanced_pc (s : ArmState) (base : BitVec 64) (kind : ByteStoreKind) (index size : Nat)
    (zero : r (.FLAG .Z) s = 1#1 ↔ index + 1 = size) :
    read_pc (advanced s base kind) =
      if index + 1 = size then base + 1000#64 else base + BitVec.ofNat 64 kind.loopStart := by
  simp only [advanced, state_simp_rules, zero]

end SszArm.Emit.Uint
