import SszArm.CodecFixedMeasureContextFrame

namespace SszArm.Codec.Fixed.MeasureFixed

open Dispatch.Block (next put)
open Delimited (MemoryFrame)
open UintCodec (widthLoad)

def statusOps : List Op := [.finish .p676, .finish .p680, .finish .p684, .finish .p688,
  .finish .p692, .finish .p696, .finish .p700, .finish .p704, .finish .p708, .finish .p712]

@[irreducible] def status (s : ArmState) : ArmState := block statusOps s

def statusMemory (s : ArmState) : ArmState :=
  write_mem_bytes 4 (r (.GPR 19#5) s + 64#64) 0#32
    (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (r (.GPR 10#5) s)
      (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s))

@[simp] theorem status_memory (s : ArmState) : (status s).mem = (statusMemory s).mem := by
  simp [status, statusOps, block, Op.effect, Return.Op.effect, next, put,
    statusMemory, state_simp_rules, BitVec.add_assoc]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

@[simp] theorem status_sp (s : ArmState) : r (.GPR 31#5) (status s) = r (.GPR 31#5) s := by
  simp [status, statusOps, block, Op.effect, Return.Op.effect, next, put,
    state_simp_rules]

@[simp] theorem status_pc (s : ArmState) : read_pc (status s) = read_pc s + 40#64 := by
  simp [status, statusOps, block, Op.effect, Return.Op.effect, next, put,
    state_simp_rules, BitVec.add_assoc]

@[simp] theorem status_program (s : ArmState) : (status s).program = s.program :=
  block_program statusOps s

@[simp] theorem status_error (s : ArmState) : read_err (status s) = read_err s :=
  block_error statusOps s

@[simp] theorem status_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (status s) = r (.SFP reg) s := by
  simp [status, statusOps, block, Op.effect, Return.Op.effect, next, put,
    state_simp_rules]

theorem status_register (s : ArmState) (reg : BitVec 5)
    (different : reg ≠ 9#5 ∧ reg ≠ 10#5 ∧ reg ≠ 31#5) :
    r (.GPR reg) (status s) = r (.GPR reg) s := by
  rcases different with ⟨h9, h10, h31⟩
  simp [status, statusOps, block, Op.effect, Return.Op.effect, next, put,
    state_simp_rules, h9, h10, h31]

theorem status_run (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureFixed.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 676#64) :
    run 10 s = status s := by
  have pcs : PCs base statusOps s := by
    change r .PC s = base + 676#64 at pc
    simp [PCs, statusOps, Op.row, Return.Op.row, Op.effect, Return.Op.effect,
      put, next, state_simp_rules, pc, BitVec.add_assoc]
  exact run_block statusOps s base code error aligned pcs

def statusWrites (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16), ((r (.GPR 19#5) s).toNat + 64, 4)]

theorem status_frame (s : ArmState) (low : 16 ≤ (r (.GPR 31#5) s).toNat)
    (resultBound : (r (.GPR 19#5) s).toNat + 72 ≤ 2^64) :
    MemoryFrame (statusWrites s) s (status s) := by
  intro address outside
  have stackApart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [statusWrites])
  have resultApart := outside ((r (.GPR 19#5) s).toNat + 64, 4) (by simp [statusWrites])
  simp only [Prod.fst, Prod.snd] at stackApart resultApart
  rw [status_memory]
  simp only [statusMemory]
  rw [BoolCodec.write_mem_bytes_frame _ _ 4 _ address (by bv_omega) (by bv_omega)]
  repeat' rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)]

theorem status_word (s : ArmState) (resultBound : (r (.GPR 19#5) s).toNat + 72 ≤ 2^64) :
    read_mem_bytes 4 (r (.GPR 19#5) s + 64#64) (status s) = 0#32 := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (status_memory s))]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ _ _ _ (by bv_omega)

theorem status_observe (s : ArmState) (resultBound : (r (.GPR 19#5) s).toNat + 72 ≤ 2^64) :
    widthLoad (status s) ((r (.GPR 19#5) s).toNat + 64) 4 = some 0 := by
  simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using
    congrArg (fun word : BitVec 32 => some word.toNat) (status_word s resultBound)

end SszArm.Codec.Fixed.MeasureFixed
