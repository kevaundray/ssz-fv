import SszArm.IndicesChunkPositionReturn

set_option autoImplicit false

namespace SszArm.Indices.ChunkPosition

/-- Exact data-movement instructions following an element_type failure. Padding
at Result+68 is copied as the instruction does, but is not a logical error field. -/
inductive ErrorCopyOp where
  | load32 | store8 | store0 | store32 | load48 | load24 | store48
  | loadPadding | store24 | storeReason
  deriving DecidableEq

def ErrorCopyOp.offset : ErrorCopyOp → Nat
  | .load32 => 64
  | .store8 => 68
  | .store0 => 72
  | .store32 => 76
  | .load48 => 80
  | .load24 => 84
  | .store48 => 88
  | .loadPadding => 92
  | .store24 => 96
  | .storeReason => 100

def ErrorCopyOp.word : ErrorCopyOp → BitVec 32
  | .load32 => 0xa94bafea#32
  | .store8 => 0xa900d674#32
  | .store0 => 0xf9000268#32
  | .store32 => 0xa9022e6a#32
  | .load48 => 0xa94cabec#32
  | .load24 => 0xf9405beb#32
  | .store48 => 0xa9032a6c#32
  | .loadPadding => 0xb940dfea#32
  | .store24 => 0xf9000e6b#32
  | .storeReason => 0x29082a69#32

def ErrorCopyOp.apply (op : ErrorCopyOp) (s : ArmState) : ArmState :=
  match op with
  | .load32 =>
      w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 192#64) s)
        (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 184#64) s)
          (w .PC (read_pc s + 4#64) s))
  | .store8 => w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 19#5) s + 8#64)
        (r (.GPR 21#5) s ++ r (.GPR 20#5) s) s)
  | .store0 => w .PC (read_pc s + 4#64)
      (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 8#5) s) s)
  | .store32 => w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 19#5) s + 32#64)
        (r (.GPR 11#5) s ++ r (.GPR 10#5) s) s)
  | .load48 =>
      w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 208#64) s)
        (w (.GPR 12#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 200#64) s)
          (w .PC (read_pc s + 4#64) s))
  | .load24 => w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 176#64) s)
      (w .PC (read_pc s + 4#64) s)
  | .store48 => w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 19#5) s + 48#64)
        (r (.GPR 10#5) s ++ r (.GPR 12#5) s) s)
  | .loadPadding => w (.GPR 10#5)
      ((read_mem_bytes 4 (r (.GPR 31#5) s + 220#64) s).zeroExtend 64)
      (w .PC (read_pc s + 4#64) s)
  | .store24 => w .PC (read_pc s + 4#64)
      (write_mem_bytes 8 (r (.GPR 19#5) s + 24#64) (r (.GPR 11#5) s) s)
  | .storeReason => w .PC (read_pc s + 4#64)
      (write_mem_bytes 8 (r (.GPR 19#5) s + 64#64)
        ((r (.GPR 10#5) s).extractLsb' 0 32 ++ (r (.GPR 9#5) s).extractLsb' 0 32) s)

theorem ErrorCopyOp.step (op : ErrorCopyOp) (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkPosition.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.offset) :
    stepi s = op.apply s := by
  have member : (op.offset, op.word) ∈ Linked.ChunkPosition.chunk0 := by
    cases op <;> decide
  have fetched := Linked.ChunkPosition.chunk0_codeAt code _ member
  cases op <;>
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl] <;>
    simp (config := {decide := true, instances := true})
      [ErrorCopyOp.apply, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
        BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc]
  all_goals first | rfl | exact w_of_w_commute (by decide)

@[simp] theorem ErrorCopyOp.program (op : ErrorCopyOp) (s : ArmState) :
    (op.apply s).program = s.program := by
  cases op <;> simp [ErrorCopyOp.apply, state_simp_rules]

@[simp] theorem ErrorCopyOp.error (op : ErrorCopyOp) (s : ArmState) :
    read_err (op.apply s) = read_err s := by
  cases op <;> simp [ErrorCopyOp.apply, state_simp_rules]

@[simp] theorem ErrorCopyOp.pc (op : ErrorCopyOp) (s : ArmState) :
    read_pc (op.apply s) = read_pc s + 4#64 := by
  cases op <;> simp [ErrorCopyOp.apply, state_simp_rules]

@[simp] theorem ErrorCopyOp.sp (op : ErrorCopyOp) (s : ArmState) :
    r (.GPR 31#5) (op.apply s) = r (.GPR 31#5) s := by
  cases op <;> simp [ErrorCopyOp.apply, state_simp_rules]

@[simp] theorem ErrorCopyOp.aligned (op : ErrorCopyOp) (s : ArmState) :
    CheckSPAlignment (op.apply s) = CheckSPAlignment s := by
  simp [CheckSPAlignment, state_simp_rules]

def applyErrorCopies : List ErrorCopyOp → ArmState → ArmState
  | [], s => s
  | op :: rest, s => applyErrorCopies rest (op.apply s)

def ErrorCopyChain : Nat → List ErrorCopyOp → Prop
  | _, [] => True
  | offset, op :: rest => op.offset = offset ∧ ErrorCopyChain (offset + 4) rest

theorem error_copies_run (ops : List ErrorCopyOp) (s : ArmState) (base : BitVec 64)
    (offset : Nat) (chain : ErrorCopyChain offset ops)
    (code : Linked.ChunkPosition.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 offset) :
    run ops.length s = applyErrorCopies ops s := by
  induction ops generalizing s offset with
  | nil => rfl
  | cons op rest ih =>
      rcases chain with ⟨first, restChain⟩
      have step := op.step s base code error aligned (by simpa [first] using pc)
      change run rest.length (stepi s) = applyErrorCopies rest (op.apply s)
      rw [step]
      apply ih (op.apply s) (offset + 4) restChain
      · exact Codec.Linked.WordsAt.preserve code (op.program s)
      · simpa using error
      · simpa using aligned
      · simp [pc, BitVec.ofNat_add, BitVec.add_assoc]

def elementErrorCopies : List ErrorCopyOp :=
  [.load32, .store8, .store0, .store32, .load48, .load24, .store48,
    .loadPadding, .store24, .storeReason]

def elementErrorCopied (s : ArmState) : ArmState := applyErrorCopies elementErrorCopies s

theorem element_error_copy_run (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkPosition.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 64#64) :
    run 10 s = elementErrorCopied s :=
  error_copies_run elementErrorCopies s base 64 (by decide) code error aligned pc

@[simp] theorem applyErrorCopies_program (ops : List ErrorCopyOp) (s : ArmState) :
    (applyErrorCopies ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => simpa [applyErrorCopies] using ih (op.apply s)

@[simp] theorem applyErrorCopies_error (ops : List ErrorCopyOp) (s : ArmState) :
    read_err (applyErrorCopies ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => simpa [applyErrorCopies] using ih (op.apply s)

@[simp] theorem applyErrorCopies_sp (ops : List ErrorCopyOp) (s : ArmState) :
    r (.GPR 31#5) (applyErrorCopies ops s) = r (.GPR 31#5) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => simpa [applyErrorCopies] using ih (op.apply s)

end SszArm.Indices.ChunkPosition
